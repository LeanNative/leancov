import Lean
import LeanCov.Cov.Types
import LeanCov.Cov.Complexity

/-! # Lean 4 Syntax-level Source Instrumenter

Parses `.lean` files with Lean's own parser (`Lean.Parser.parseHeader` + `parseCommand`),
computes McCabe CC and Cognitive Complexity per executable declaration, and splices lightweight
source-level coverage probes (`LeanCov.hit`, `LeanCov.cond`, `leancov_hit%`) using exact byte
offsets so formatting, comments, and line numbers are preserved. -/

namespace LeanCov.Cov
open Lean Parser

/-- A byte-range splice on the source text.
- If `replaceLen == 0`: wraps `[startPos, endPos)` with `openText` at `startPos` and `closeText` at `endPos`.
- If `replaceLen > 0`: replaces bytes `[startPos, startPos + replaceLen)` with `openText` (and ignores `closeText`). -/
private structure Edit where
  startPos : Nat
  endPos : Nat
  seq : Nat
  openText : String
  closeText : String := ""
  replaceLen : Nat := 0
  deriving Repr, Inhabited

private inductive SpliceEvent where
  | close (pos : Nat) (spanStart : Nat) (seq : Nat) (text : String)
  | open_ (pos : Nat) (spanEnd : Nat) (seq : Nat) (text : String)
  | replace (pos : Nat) (len : Nat) (seq : Nat) (text : String)

private def SpliceEvent.pos : SpliceEvent → Nat
  | .close p .. | .open_ p .. | .replace p .. => p

private def SpliceEvent.lt (a b : SpliceEvent) : Bool :=
  if a.pos != b.pos then a.pos < b.pos
  else match a, b with
    -- closes come first at the same byte, innermost (largest spanStart, then largest seq) first
    | .close _ sa qa _, .close _ sb qb _ => if sa != sb then sa > sb else qa > qb
    | .close .., _ => true
    | _, .close .. => false
    -- opens come before replacements at the same byte so outer wrappers wrap replaced tokens
    | .open_ _ ea qa _, .open_ _ eb qb _ => if ea != eb then ea > eb else qa < qb
    | .open_ .., .replace .. => true
    | .replace .., .open_ .. => false
    -- replacements come last
    | .replace _ _ qa _, .replace _ _ qb _ => qa < qb

/-- Apply nested wrap edits and non-overlapping token replacements to UTF-8 source bytes. -/
private def applyEdits (src : String) (edits : Array Edit) : String := Id.run do
  if edits.isEmpty then return src
  let mut events : Array SpliceEvent := Array.mkEmpty (edits.size * 2)
  for e in edits do
    if e.replaceLen > 0 then
      events := events.push (.replace e.startPos e.replaceLen e.seq e.openText)
    else
      if !e.openText.isEmpty then
        events := events.push (.open_ e.startPos e.endPos e.seq e.openText)
      if !e.closeText.isEmpty then
        events := events.push (.close e.endPos e.startPos e.seq e.closeText)
  let sorted := events.qsort SpliceEvent.lt
  let bytes := src.toUTF8
  let mut out := ByteArray.emptyWithCapacity (bytes.size + edits.size * 32)
  let mut cursor : Nat := 0
  for ev in sorted do
    let p := min ev.pos bytes.size
    if p > cursor then
      out := out ++ bytes.extract cursor p
      cursor := p
    match ev with
    | .close _ _ _ txt | .open_ _ _ _ txt =>
      out := out ++ txt.toUTF8
    | .replace _ len _ txt =>
      out := out ++ txt.toUTF8
      cursor := min (p + len) bytes.size
  if cursor < bytes.size then
    out := out ++ bytes.extract cursor bytes.size
  return String.fromUTF8! out

/-- Source instrumentation configuration. -/
structure InstrumentConfig where
  /-- Relative-path substrings to skip (e.g. `["Proofs/", "Test.lean"]`). -/
  exclude : Array String := #[]
  /-- Additional Lean modules to load into the parser environment for custom syntax/macros. -/
  extraImports : Array Name := #[]
  /-- Whether to also instrument `&&` and `||` short-circuit conditions. -/
  instrumentBoolOps : Bool := true
  /-- When `true`, only measure complexity and sites without writing instrumented files. -/
  analyzeOnly : Bool := false
  deriving Inhabited

private structure FileState where
  file : String
  src : String
  fileMap : FileMap
  nextSiteId : Nat
  nextSeq : Nat := 0
  sites : Array Site := #[]
  declSiteIds : Array Nat := #[]
  edits : Array Edit := #[]
  decl : String := ""
  instrumentBoolOps : Bool := true

private abbrev InstM := StateM FileState

private def allocSite (pos : String.Pos.Raw) (kind : BranchKind) (nesting : Nat) : InstM Nat := do
  let s ← get
  let id := s.nextSiteId
  let p := s.fileMap.toPosition pos
  let site : Site := {
    id, file := s.file, decl := s.decl, line := p.line, col := p.column + 1, kind, nesting
  }
  set { s with
    nextSiteId := id + 1
    sites := s.sites.push site
    declSiteIds := s.declSiteIds.push id }
  return id

private def addWrap (startPos endPos : Nat) (openText : String) (closeText : String := "") : InstM Unit := do
  modify fun s =>
    let q := s.nextSeq
    { s with nextSeq := q + 1, edits := s.edits.push { startPos, endPos, seq := q, openText, closeText } }

private def addReplace (startPos len : Nat) (text : String) : InstM Unit := do
  modify fun s =>
    let q := s.nextSeq
    { s with nextSeq := q + 1, edits := s.edits.push { startPos, endPos := startPos + len, seq := q, openText := text, replaceLen := len } }

private def sliceOf (stx : Syntax) : InstM String := do
  let s ← get
  match stx.getPos?, stx.getTailPos? with
  | some a, some b =>
    let bytes := s.src.toUTF8
    return String.fromUTF8! (bytes.extract a.byteIdx (min b.byteIdx bytes.size))
  | _, _ => return ""

private def isDoSeq (stx : Syntax) : Bool :=
  stx.getKind == `Lean.Parser.Term.doSeqIndent || stx.getKind == `Lean.Parser.Term.doSeqBracketed

private def firstDoItemSpan? (seq : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) :=
  match seq.getKind with
  | `Lean.Parser.Term.doSeqIndent =>
    match seq.getPos?, seq.getTailPos? with
    | some a, some b => some (a, b)
    | _, _ => none
  | `Lean.Parser.Term.doSeqBracketed =>
    -- #[atom("{"), null(items), atom("}")]
    if seq.getNumArgs ≥ 2 then
      match (seq.getArg 1).getPos?, (seq.getArg 1).getTailPos? with
      | some a, some b => some (a, b)
      | _, _ => none
    else none
  | _ => none

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private def colOf (pos : String.Pos.Raw) : InstM Nat := do
  return ((← get).fileMap.toPosition pos).column

private def lineOf (pos : String.Pos.Raw) : InstM Nat := do
  return ((← get).fileMap.toPosition pos).line

/-- True if only spaces/tabs precede `bytePos` on its line in the original source. -/
private def isLineStart (bytePos : Nat) : InstM Bool := do
  let bytes := (← get).src.toUTF8
  let mut i := min bytePos bytes.size
  while i > 0 do
    i := i - 1
    let c := bytes.get! i
    if c == 10 then return true -- '\n'
    if c != 32 && c != 9 then return false
  return true

private def emitDoProbe (seq : Syntax) (kind : BranchKind) (nesting : Nat) : InstM (Option Nat) := do
  if let some (a, b) := firstDoItemSpan? seq then
    let id ← allocSite a kind nesting
    if ← isLineStart a.byteIdx then
      let col ← colOf a
      addWrap a.byteIdx b.byteIdx s!"leancov_hit% {id};\n{spaces col}"
    else if (← lineOf a) != (← lineOf b) && seq.getKind != `Lean.Parser.Term.doSeqBracketed then
      let col ← colOf a
      addWrap a.byteIdx b.byteIdx s!"\n{spaces col}leancov_hit% {id};\n{spaces col}"
    else
      addWrap a.byteIdx b.byteIdx s!"leancov_hit% {id}; "
    return some id
  return none

private def emitDoProbe_ (seq : Syntax) (kind : BranchKind) (nesting : Nat) : InstM Unit := do
  let _ ← emitDoProbe seq kind nesting

private partial def unwrapParen (s : Syntax) : Syntax :=
  if s.getKind == `Lean.Parser.Term.paren && s.getNumArgs ≥ 2 then
    unwrapParen (s.getArg 1)
  else s

private def isBoolOp (s : Syntax) : Bool :=
  let k := (unwrapParen s).getKind
  k == `«term_&&_» || k == `«term_||_»

private def emitCondWrap (operand : Syntax) (tKind fKind : BranchKind) (nesting : Nat) : InstM Unit := do
  if let (some a, some b) := (operand.getPos?, operand.getTailPos?) then
    let tId ← allocSite a tKind nesting
    let fId ← allocSite a fKind nesting
    if (← lineOf a) != (← lineOf b) then
      let col ← colOf a
      addWrap a.byteIdx b.byteIdx s!"(LeanCov.cond {tId} {fId} (\n{spaces col}" "))"
    else
      addWrap a.byteIdx b.byteIdx s!"(LeanCov.cond {tId} {fId} (" "))"

/-- Add semicolons after all but the last `doSeqItem` of a `doSeqIndent` so it can sit inside `{ ... }`. -/
private def addSemisBetweenDoItems (seq : Syntax) : InstM Unit := do
  if seq.getKind == `Lean.Parser.Term.doSeqIndent && seq.getNumArgs ≥ 1 then
    let items := (seq.getArg 0).getArgs
    for i in [:items.size] do
      if i + 1 < items.size then
        if let some tail := items[i]!.getTailPos? then
          addWrap tail.byteIdx tail.byteIdx "" ";"

/-- Instrument a one-armed `if c then seq` (or trailing `else if c then seq` with no `else`)
without disturbing multi-line `doSeqIndent` layout. -/
private def emitOneArmedDoIfBranch (anchorTok seq : Syntax) (nesting : Nat) : InstM Unit := do
  if let (some a, some b) := (seq.getPos?, seq.getTailPos?) then
    let tId ← allocSite a .ifThen nesting
    let fId ← allocSite a .ifElse nesting
    if seq.getKind == `Lean.Parser.Term.doSeqBracketed then
      if let some (ia, ib) := firstDoItemSpan? seq then
        if ← isLineStart ia.byteIdx then
          let icol ← colOf ia
          addWrap ia.byteIdx ib.byteIdx s!"leancov_hit% {tId};\n{spaces icol}"
        else
          addWrap ia.byteIdx ib.byteIdx s!"leancov_hit% {tId}; "
      addWrap a.byteIdx b.byteIdx "" s!" else \{ leancov_hit% {fId}; pure () }"
    else if (← lineOf a) != (← lineOf b) then
      -- Multi-line `doSeqIndent`: prefer unbraced `else` aligned with `if`/`else if` when it starts its line
      let anchorAtStart ← match anchorTok.getPos? with
        | some ap => isLineStart ap.byteIdx
        | none => pure false
      if anchorAtStart then
        let anchorCol ← match anchorTok.getPos? with
          | some ap => colOf ap
          | none => colOf a
        if ← isLineStart a.byteIdx then
          let col ← colOf a
          addWrap a.byteIdx b.byteIdx s!"leancov_hit% {tId};\n{spaces col}" s!"\n{spaces anchorCol}else \{ leancov_hit% {fId}; pure () }"
        else
          addWrap a.byteIdx b.byteIdx s!"leancov_hit% {tId}; " s!"\n{spaces anchorCol}else \{ leancov_hit% {fId}; pure () }"
      else
        addWrap a.byteIdx b.byteIdx "{ " s!" } else \{ leancov_hit% {fId}; pure () }"
        addWrap a.byteIdx b.byteIdx s!"leancov_hit% {tId}; "
        addSemisBetweenDoItems seq
    else
      -- Single-line `thenSeq`
      addWrap a.byteIdx b.byteIdx "{ " s!" } else \{ leancov_hit% {fId}; pure () }"
      addWrap a.byteIdx b.byteIdx s!"leancov_hit% {tId}; "

private def emitTermWrap (term : Syntax) (kind : BranchKind) (nesting : Nat) : InstM Unit := do
  if term.getKind == `Lean.Parser.Term.byTactic then return
  if let (some a, some b) := (term.getPos?, term.getTailPos?) then
    let id ← allocSite a kind nesting
    if (← lineOf a) != (← lineOf b) then
      let col ← colOf a
      addWrap a.byteIdx b.byteIdx s!"(leancov_term% {id} (\n{spaces col}" "))"
    else
      addWrap a.byteIdx b.byteIdx s!"(leancov_term% {id} (" "))"

private def skipWalkKind (k : SyntaxNodeKind) : Bool :=
  k == `Lean.Parser.Term.byTactic ||
  k == `Lean.Parser.Term.typeSpec ||
  k == `Lean.Parser.Termination.suffix ||
  k == `Lean.Parser.Command.declModifiers ||
  k == `Lean.Parser.Term.explicitBinder ||
  k == `Lean.Parser.Term.implicitBinder ||
  k == `Lean.Parser.Term.strictImplicitBinder ||
  k == `Lean.Parser.Term.instBinder ||
  k == `Lean.Parser.Term.have ||
  k == `Lean.Parser.Term.doHave ||
  k == `Lean.Parser.Term.suffices ||
  k == `Lean.Parser.Term.quotedName ||
  k == `Lean.Parser.Term.doubleQuotedName ||
  k == `Lean.Parser.Term.syntaxQuotation ||
  k == `Lean.Parser.Term.stxQuot ||
  k == `Lean.Parser.Term.dynamicQuot

mutual

private partial def walkTermIf (k : SyntaxNodeKind) (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  let n := args.size
  unless n ≥ 6 do
    for a in args do walkBody a nesting
    return
  let savedBool := (← get).instrumentBoolOps
  if k == `termDepIfThenElse then
    modify fun s => { s with instrumentBoolOps := false }
  walkBody args[n - 5]! nesting
  if k == `termDepIfThenElse then
    modify fun s => { s with instrumentBoolOps := savedBool }
  let thenStx := args[n - 3]!
  let elseStx := args[n - 1]!
  emitTermWrap thenStx .ifThen nesting
  walkBody thenStx (nesting + 1)
  if elseStx.getKind == `termIfThenElse || elseStx.getKind == `termDepIfThenElse || elseStx.getKind == `termIfLet then
    walkBody elseStx nesting
  else
    emitTermWrap elseStx .ifElse nesting
    walkBody elseStx (nesting + 1)

private partial def walkDoIf (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  unless args.size ≥ 6 do
    for a in args do walkBody a nesting
    return
  walkBody args[1]! nesting
  let thenSeq := args[3]!
  let elseIfs := args[4]!.getArgs
  let elseOpt := args[5]!
  let hasElse := elseOpt.getNumArgs ≥ 2
  if !hasElse && elseIfs.isEmpty then
    emitOneArmedDoIfBranch args[0]! thenSeq nesting
    walkBody thenSeq (nesting + 1)
    return
  emitDoProbe_ thenSeq .ifThen nesting
  walkBody thenSeq (nesting + 1)
  for idx in [:elseIfs.size] do
    let ei := elseIfs[idx]!
    if ei.getNumArgs ≥ 4 then
      walkBody (ei.getArg 1) nesting
      let eiSeq := ei.getArg 3
      if !hasElse && idx + 1 == elseIfs.size then
        emitOneArmedDoIfBranch ei eiSeq nesting
      else
        emitDoProbe_ eiSeq .ifThen nesting
      walkBody eiSeq (nesting + 1)
  if hasElse then
    let elseSeq := elseOpt.getArg 1
    emitDoProbe_ elseSeq .ifElse nesting
    walkBody elseSeq (nesting + 1)

private partial def walkDoUnless (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  unless args.size ≥ 4 do
    for a in args do walkBody a nesting
    return
  let uTok := args[0]!
  let cond := args[1]!
  let doTok := args[2]!
  let bodySeq := args[3]!
  let (some ua, some ub, some da, some db, some ba, some bb) :=
    (uTok.getPos?, uTok.getTailPos?, doTok.getPos?, doTok.getTailPos?, bodySeq.getPos?, bodySeq.getTailPos?)
    | for a in args do walkBody a nesting
      return
  let skipId ← allocSite ua .unlessSkip nesting
  let enterId ← allocSite ba .unlessEnter nesting
  addReplace ua.byteIdx (ub.byteIdx - ua.byteIdx) "if"
  walkBody cond nesting
  if bodySeq.getKind == `Lean.Parser.Term.doSeqBracketed then
    addReplace da.byteIdx (db.byteIdx - da.byteIdx) s!"then \{ leancov_hit% {skipId}; pure () } else"
    if let some (ia, ib) := firstDoItemSpan? bodySeq then
      if ← isLineStart ia.byteIdx then
        let icol ← colOf ia
        addWrap ia.byteIdx ib.byteIdx s!"leancov_hit% {enterId};\n{spaces icol}"
      else
        addWrap ia.byteIdx ib.byteIdx s!"leancov_hit% {enterId}; "
  else if ← isLineStart ba.byteIdx then
    let col ← colOf ba
    addReplace da.byteIdx (db.byteIdx - da.byteIdx) s!"then \{ leancov_hit% {skipId}; pure () } else"
    addWrap ba.byteIdx bb.byteIdx s!"leancov_hit% {enterId};\n{spaces col}"
  else
    addReplace da.byteIdx (db.byteIdx - da.byteIdx) s!"then \{ leancov_hit% {skipId}; pure () } else \{"
    addWrap ba.byteIdx bb.byteIdx s!"leancov_hit% {enterId}; " " }"
    if (← lineOf ba) != (← lineOf bb) then
      addSemisBetweenDoItems bodySeq
  walkBody bodySeq (nesting + 1)

private partial def walkDoLoop (stx : Syntax) (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  for i in [:args.size] do
    let a := args[i]!
    if i + 1 < args.size then
      walkBody a nesting
      continue
    let trackSkip ← match stx.getPos?, stx.getTailPos? with
      | some la, some _ => isLineStart la.byteIdx
      | _, _ => pure false
    match trackSkip, firstDoItemSpan? a, stx.getPos?, stx.getTailPos? with
    | true, some (ba, bb), some la, some lb =>
      let bodyId ← allocSite ba .loopBody nesting
      let skipId ← allocSite la .loopSkip nesting
      let lcol ← colOf la
      let flag := s!"__lc_loop_{bodyId}"
      addWrap la.byteIdx lb.byteIdx
        s!"let mut {flag} := false;\n{spaces lcol}"
        s!"\n{spaces lcol}if !{flag} then \{ leancov_hit% {skipId}; pure PUnit.unit };"
      if ← isLineStart ba.byteIdx then
        let bcol ← colOf ba
        addWrap ba.byteIdx bb.byteIdx s!"leancov_hit% {bodyId};\n{spaces bcol}{flag} := true;\n{spaces bcol}"
      else if a.getKind == `Lean.Parser.Term.doSeqBracketed then
        addWrap ba.byteIdx bb.byteIdx s!"leancov_hit% {bodyId}; {flag} := true; "
      else if (← lineOf ba) != (← lineOf bb) then
        let bcol ← colOf ba
        addWrap ba.byteIdx bb.byteIdx s!"\n{spaces bcol}leancov_hit% {bodyId};\n{spaces bcol}{flag} := true;\n{spaces bcol}"
      else
        addWrap ba.byteIdx bb.byteIdx s!"\{ leancov_hit% {bodyId}; {flag} := true; " " }"
    | _, _, _, _ =>
      emitDoProbe_ a .loopBody nesting
    walkBody a (nesting + 1)

private partial def walkDoPatDecl (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  if args.size ≥ 4 then walkBody args[3]! nesting
  if args.size ≥ 5 then
    let fb := args[4]!
    if fb.getNumArgs ≥ 2 then
      let fallbackSeq := fb.getArg 1
      emitDoProbe_ fallbackSeq .letElseFail nesting
      walkBody fallbackSeq (nesting + 1)
      if fb.getNumArgs ≥ 3 then
        let contOpt := fb.getArg 2
        if contOpt.getNumArgs ≥ 1 then
          let contSeq := contOpt.getArg 0
          emitDoProbe_ contSeq .letElseOk nesting
          walkBody contSeq nesting

private partial def walkAt (args : Array Syntax) (idx nesting : Nat) : InstM Unit := do
  if idx < args.size then walkBody args[idx]! nesting

private partial def walkDoIfProp (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  unless args.size ≥ 2 do return
  let hasProofBinder := args[0]!.getNumArgs > 0
  let savedBool := (← get).instrumentBoolOps
  if hasProofBinder then modify fun s => { s with instrumentBoolOps := false }
  walkBody args[1]! nesting
  if hasProofBinder then modify fun s => { s with instrumentBoolOps := savedBool }

private partial def walkDoLetElse (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  if args.size ≥ 6 then walkBody args[5]! nesting
  if args.size ≥ 8 then
    emitDoProbe_ args[7]! .letElseFail nesting
    walkBody args[7]! (nesting + 1)
  unless args.size ≥ 9 do return
  let contOpt := args[8]!
  if contOpt.getNumArgs ≥ 1 then
    let contSeq := contOpt.getArg 0
    emitDoProbe_ contSeq .letElseOk nesting
    walkBody contSeq nesting

private partial def walkDoRepeat (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  for i in [:args.size] do
    let a := args[i]!
    if i + 1 == args.size then
      emitDoProbe_ a .loopBody nesting
      walkBody a (nesting + 1)
    else
      walkBody a nesting

private partial def walkDoCatch (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  if args.size > 0 then
    let body := args[args.size - 1]!
    emitDoProbe_ body .catchBody nesting
    walkBody body (nesting + 1)

private partial def walkMatchAlt (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  unless args.size ≥ 4 do return
  let rhs := args[3]!
  if isDoSeq rhs then emitDoProbe_ rhs .matchArm nesting
  else emitTermWrap rhs .matchArm nesting
  walkBody rhs (nesting + 1)

private partial def walkBoolOp (k : SyntaxNodeKind) (args : Array Syntax) (nesting : Nat) : InstM Unit := do
  unless args.size ≥ 3 do
    for a in args do walkBody a nesting
    return
  if (← get).instrumentBoolOps then
    let (tKind, fKind) :=
      if k == `«term_&&_» then (BranchKind.andTrue, BranchKind.andFalse)
      else (BranchKind.orTrue, BranchKind.orFalse)
    if !isBoolOp args[0]! then emitCondWrap args[0]! tKind fKind nesting
    if !isBoolOp args[2]! then emitCondWrap args[2]! tKind fKind nesting
  walkBody args[0]! nesting
  walkBody args[2]! nesting

private partial def walkBody (stx : Syntax) (nesting : Nat) : InstM Unit := do
  let .node _ k args := stx | return
  if skipWalkKind k then return
  match k with
  | `Lean.Parser.Term.typeAscription => walkAt args 1 nesting
  | `termIfThenElse | `termDepIfThenElse | `termIfLet => walkTermIf k args nesting
  | `Lean.Parser.Term.doIfProp => walkDoIfProp args nesting
  | `Lean.Parser.Term.doIfLet => walkAt args 2 nesting
  | `Lean.Parser.Term.doIf => walkDoIf args nesting
  | `Lean.Parser.Term.doUnless => walkDoUnless args nesting
  | `Lean.Parser.Term.doLetElse => walkDoLetElse args nesting
  | `Lean.Parser.Term.doFor | `Lean.Parser.Term.doWhile => walkDoLoop stx args nesting
  | `Lean.Parser.Term.doRepeat => walkDoRepeat args nesting
  | `Lean.Parser.Term.doCatch => walkDoCatch args nesting
  | `Lean.Parser.Term.matchAlt => walkMatchAlt args nesting
  | `«term_&&_» | `«term_||_» => walkBoolOp k args nesting
  | `Lean.Parser.Term.letIdDecl | `Lean.Parser.Term.letPatDecl => walkAt args 4 nesting
  | `Lean.Parser.Term.doIdDecl => walkAt args 3 nesting
  | `Lean.Parser.Term.doPatDecl => walkDoPatDecl args nesting
  | `Lean.Parser.Term.structInstField =>
    if args.size ≥ 2 then walkBody args[args.size - 1]! nesting
  | _ =>
    for a in args do walkBody a nesting

end

/-- Detect modifiers that mean a declaration is compile-time/proof/extern only and should not be instrumented. -/
private def shouldSkipModifiers (mods : Syntax) (src : String) : Bool :=
  match mods.getPos?, mods.getTailPos? with
  | some a, some b =>
    let bytes := src.toUTF8
    let txt := String.fromUTF8! (bytes.extract a.byteIdx (min b.byteIdx bytes.size))
    let has (w : String) := (txt.splitOn w).length > 1
    has "@[extern" || has "noncomputable" || has "meta " || has "\nmeta " || has "macro" || has "unsafe "
  | _, _ => false

private partial def findTypeSpec (s : Syntax) : Option Syntax :=
  if s.getKind == `Lean.Parser.Term.typeSpec then some s
  else s.getArgs.findSome? findTypeSpec

/-- Return `true` when a declaration's explicit return type is obviously non-computational (`Prop`, `Type`, `Sort`, `Decidable`). -/
private def isNonComputationalSig (sig : Syntax) (src : String) : Bool :=
  match findTypeSpec sig with
  | none => false
  | some ts =>
    match ts.getPos?, ts.getTailPos? with
    | some a, some b =>
      let bytes := src.toUTF8
      let raw := String.fromUTF8! (bytes.extract a.byteIdx (min b.byteIdx bytes.size))
      -- Examine the final codomain after the last `→` or `->`
      let afterColon := (raw.drop 1).toString.trimAscii.copy
      let parts := afterColon.splitOn "→"
      let last := (parts.getLast?.getD afterColon).splitOn "->" |>.getLast?.getD afterColon |>.trimAscii.copy
      last == "Prop" || last == "Type" || last.startsWith "Type " || last.startsWith "Sort" ||
      last.startsWith "Decidable" || last.startsWith "Nonempty" || last.startsWith "Subsingleton" ||
      last.startsWith "Inhabited" || last.startsWith "Lean.Elab." || last.startsWith "Elab." ||
      last.startsWith "CommandElab" || last.startsWith "TermElab" || last.startsWith "Macro"
    | _, _ => false

/-- Check whether `valStx` has a `by` tactic proof as its top-level body. -/
private def isTacticBody (valStx : Syntax) : Bool :=
  match valStx.getKind with
  | `Lean.Parser.Command.declValSimple =>
    valStx.getNumArgs ≥ 2 && (valStx.getArg 1).getKind == `Lean.Parser.Term.byTactic
  | _ => false

private def declIdName (idStx : Syntax) : String :=
  if idStx.getNumArgs ≥ 1 then
    match idStx.getArg 0 with
    | .ident _ _ n _ => n.toString
    | _ => "<anon>"
  else "<anon>"

private def qualifyName (ns : List String) (name : String) : String :=
  if ns.isEmpty || name.startsWith "_root_." then name
  else ".".intercalate (ns.reverse ++ [name])

private def headerIsModule (hdr : Syntax) : Bool :=
  hdr.getNumArgs > 0 && (hdr.getArg 0).getNumArgs > 0

private def hasSigBinders (sigStx : Syntax) : Bool :=
  sigStx.getNumArgs ≥ 1 && (sigStx.getArg 0).getNumArgs > 0

/-- True if `valStx` is a `fun x => rhs` whose inner `rhs` we can wrap with `.fnEntry`. -/
private def basicFunRhs? (body : Syntax) : Option Syntax :=
  if body.getKind == `Lean.Parser.Term.fun && body.getNumArgs ≥ 2 then
    let inner := body.getArg 1
    if inner.getKind == `Lean.Parser.Term.basicFun && inner.getNumArgs ≥ 4 then
      some (inner.getArg 3)
    else none
  else none

/-- Instrument one `def` or `instance` declaration, returning its `FuncInfo` if eligible. -/
private def instrumentDecl (ns : List String) (cmd : Syntax) (mods inner : Syntax) : InstM (Option FuncInfo) := do
  let s ← get
  if shouldSkipModifiers mods s.src then return none
  let k := inner.getKind
  let isDef := k == `Lean.Parser.Command.definition
  let isInst := k == `Lean.Parser.Command.instance
  unless isDef || isInst do return none
  -- Extract name, optDeclSig, declVal
  let (rawName, sigStx, valStx) ←
    if isDef && inner.getNumArgs ≥ 4 then
      pure (declIdName (inner.getArg 1), inner.getArg 2, inner.getArg 3)
    else if isInst && inner.getNumArgs ≥ 5 then
      -- `instance`: #[attr?, "instance", prio?, declIdOpt, optDeclSig, declVal]
      let idOpt := inner.getArg 3
      let sig := inner.getArg 4
      let val := inner.getArg 5
      let nm :=
        if idOpt.getNumArgs ≥ 1 then declIdName (idOpt.getArg 0)
        else
          let sigTxt := match sig.getPos?, sig.getTailPos? with
            | some a, some b => String.fromUTF8! (s.src.toUTF8.extract a.byteIdx (min b.byteIdx s.src.toUTF8.size))
            | _, _ => ""
          let clean := (sigTxt.replace "\n" " ").trimAscii.copy
          let short := String.ofList (clean.toList.take 48)
          s!"(instance {short})"
      pure (nm, sig, val)
    else return none
  if isNonComputationalSig sigStx s.src then return none
  if isTacticBody valStx then return none
  -- Compute complexity and line range from original AST
  let comp := measureComplexity valStx
  let (startLine, endLine) := match inner.getPos?, cmd.getTailPos? with
    | some a, some b => ((s.fileMap.toPosition a).line, (s.fileMap.toPosition b).line)
    | _, _ => (1, 1)
  let qname := qualifyName ns rawName
  modify fun st => { st with decl := qname, declSiteIds := #[] }
  -- Walk the declaration value
  let mut isPureConstant := false
  match valStx.getKind with
  | `Lean.Parser.Command.declValSimple =>
    -- #[":=", bodyTerm, terminationSuffix, whereDeclsOpt]
    if valStx.getNumArgs ≥ 2 then
      let body := valStx.getArg 1
      walkBody body 0
      if valStx.getNumArgs ≥ 4 then
        walkBody (valStx.getArg 3) 0
      -- Straight-line callable function with 0 branch sites: attach a function-entry probe.
      -- Skip pure 0-arg constants/CAFs (e.g. `def nonceSize := 12`, `instance : Foo := ⟨...⟩`)
      -- so module initializers never inflate function/branch coverage.
      if (← get).declSiteIds.isEmpty then
        if body.getKind == `Lean.Parser.Term.do && body.getNumArgs ≥ 2 then
          emitDoProbe_ (body.getArg 1) .fnEntry 0
        else if let some lamRhs := basicFunRhs? body then
          emitTermWrap lamRhs .fnEntry 0
        else if isDef && hasSigBinders sigStx then
          emitTermWrap body .fnEntry 0
        else
          isPureConstant := true
  | `Lean.Parser.Command.declValEqns =>
    walkBody valStx 0
  | `Lean.Parser.Command.whereStructInst =>
    -- `instance : Foo where f := ...` — instrument each field's RHS
    walkBody valStx 0
    if (← get).declSiteIds.isEmpty then
      isPureConstant := true
  | _ => pure ()
  if isPureConstant then return none
  let siteIds := (← get).declSiteIds
  return some {
    name := qname
    file := s.file
    line := startLine
    endLine := endLine
    lines := if endLine ≥ startLine then endLine - startLine + 1 else 1
    cc := comp.cc
    cognitive := comp.cognitive
    siteIds := siteIds
  }

private def identParts (s : Syntax) : List String :=
  match s with
  | .ident _ _ n _ => n.components.map Name.toString
  | _ => []

private def pushNamespaceScope (cmd : Syntax) (scopeStack : List (Bool × List String)) (ns : List String) :
    List (Bool × List String) × List String :=
  if cmd.getNumArgs ≥ 2 then
    let parts := identParts (cmd.getArg 1)
    ((true, parts) :: scopeStack, parts.reverse ++ ns)
  else (scopeStack, ns)

private def pushSectionScope (cmd : Syntax) (scopeStack : List (Bool × List String)) (ns : List String) :
    List (Bool × List String) × List String :=
  let parts :=
    if cmd.getNumArgs ≥ 2 && (cmd.getArg 1).getNumArgs ≥ 1 then
      identParts ((cmd.getArg 1).getArg 0)
    else []
  ((false, parts) :: scopeStack, ns)

private def popScope (scopeStack : List (Bool × List String)) (ns : List String) :
    List (Bool × List String) × List String :=
  match scopeStack with
  | (isNs, parts) :: rest => (rest, if isNs then ns.drop parts.length else ns)
  | [] => ([], [])

private def stepScope? (cmd : Syntax) (scopeStack : List (Bool × List String)) (ns : List String) :
    Option (List (Bool × List String) × List String) :=
  match cmd.getKind with
  | `Lean.Parser.Command.namespace => some (pushNamespaceScope cmd scopeStack ns)
  | `Lean.Parser.Command.section => some (pushSectionScope cmd scopeStack ns)
  | `Lean.Parser.Command.end => some (popScope scopeStack ns)
  | _ => none

private def walkDeclCommand (cmd : Syntax) (ns : List String) (funcs : Array FuncInfo) :
    InstM (Array FuncInfo) := do
  unless cmd.getNumArgs ≥ 2 do return funcs
  match ← instrumentDecl ns cmd (cmd.getArg 0) (cmd.getArg 1) with
  | some fi => return funcs.push fi
  | none => return funcs

mutual

private partial def walkMutualCommand (cmd : Syntax) (scopeStack : List (Bool × List String)) (ns : List String)
    (funcs : Array FuncInfo) : InstM (Array FuncInfo) := do
  -- #[atom("mutual"), null(decls), atom("end")]
  let mut fs := funcs
  if cmd.getNumArgs ≥ 2 then
    for d in (cmd.getArg 1).getArgs do
      let (_, _, fs') ← walkCommand d scopeStack ns fs
      fs := fs'
  return fs

/-- Walk top-level commands, maintaining the `namespace` / `section` stack. -/
private partial def walkCommand (cmd : Syntax) (scopeStack : List (Bool × List String)) (ns : List String)
    (funcs : Array FuncInfo) : InstM (List (Bool × List String) × List String × Array FuncInfo) := do
  if let some (ss, ns') := stepScope? cmd scopeStack ns then
    return (ss, ns', funcs)
  match cmd.getKind with
  | `Lean.Parser.Command.in =>
    -- `section ... in cmd` / `open ... in cmd` / `attribute ... in cmd`
    if cmd.getNumArgs ≥ 3 then
      walkCommand (cmd.getArg 2) scopeStack ns funcs
    else
      return (scopeStack, ns, funcs)
  | `Lean.Parser.Command.mutual =>
    return (scopeStack, ns, ← walkMutualCommand cmd scopeStack ns funcs)
  | `Lean.Parser.Command.declaration =>
    return (scopeStack, ns, ← walkDeclCommand cmd ns funcs)
  | _ => return (scopeStack, ns, funcs)

end

/-- Result of instrumenting a single `.lean` source file. -/
structure FileResult where
  instrumented : String
  sites : Array Site
  functions : Array FuncInfo
  nextSiteId : Nat
  skippedReason : Option String := none

/-- Parse and instrument a single `.lean` file in memory using parser environment `env`. -/
def instrumentSource (env : Environment) (relFile src : String) (startSiteId : Nat)
    (cfg : InstrumentConfig := {}) : IO FileResult := do
  let ic := mkInputContext src relFile
  let (hdr, pstate, msgs0) ← parseHeader ic
  if msgs0.hasErrors then
    let err ← msgs0.toList.mapM (·.toString)
    return { instrumented := src, sites := #[], functions := #[], nextSiteId := startSiteId,
             skippedReason := some ("header parse error: " ++ "; ".intercalate err) }
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut ps := pstate
  let mut msgs := msgs0
  let mut cmds : Array Syntax := #[]
  repeat
    let (cmd, ps', msgs') := parseCommand ic pmctx ps msgs
    ps := ps'
    msgs := msgs'
    if isTerminalCommand cmd then break
    cmds := cmds.push cmd
  if msgs.hasErrors then
    let err ← msgs.toList.filter (·.severity == .error) |>.mapM (·.toString)
    return { instrumented := src, sites := #[], functions := #[], nextSiteId := startSiteId,
             skippedReason := some ("parse error: " ++ "; ".intercalate (err.take 2)) }
  let initState : FileState := {
    file := relFile, src, fileMap := ic.fileMap, nextSiteId := startSiteId,
    instrumentBoolOps := cfg.instrumentBoolOps
  }
  let run : InstM (Array FuncInfo) := do
    let mut scopeStack : List (Bool × List String) := []
    let mut ns : List String := []
    let mut funcs : Array FuncInfo := #[]
    for cmd in cmds do
      let (ss, ns', fs) ← walkCommand cmd scopeStack ns funcs
      scopeStack := ss
      ns := ns'
      funcs := fs
    return funcs
  let (funcs, st) := run.run initState
  if cfg.analyzeOnly || st.edits.isEmpty then
    return { instrumented := src, sites := st.sites, functions := funcs, nextSiteId := st.nextSiteId }
  -- Inject `import LeanCov.DoSyntax` immediately after the module header
  let hdrEnd := (hdr.raw.getTailPos?.map (·.byteIdx)).getD 0
  let importLine :=
    if headerIsModule hdr.raw then
      if hdrEnd == 0 then "public import LeanCov.DoSyntax\n" else "\npublic import LeanCov.DoSyntax\n"
    else
      if hdrEnd == 0 then "import LeanCov.DoSyntax\n" else "\nimport LeanCov.DoSyntax\n"
  let headerEdit : Edit := { startPos := hdrEnd, endPos := hdrEnd, seq := 0, openText := importLine }
  -- Shift existing edit sequences so headerEdit is first if hdrEnd == 0
  let shifted := st.edits.map fun e => { e with seq := e.seq + 1 }
  let rewritten := applyEdits src (#[headerEdit] ++ shifted)
  return { instrumented := rewritten, sites := st.sites, functions := funcs, nextSiteId := st.nextSiteId }

private def wrapMainExpr (fileMap : FileMap) (e : Syntax) (acc : Array Edit) : Array Edit :=
  match e.getPos?, e.getTailPos? with
  | some a, some b =>
    let la := (fileMap.toPosition a).line
    let lb := (fileMap.toPosition b).line
    let col := (fileMap.toPosition a).column
    let openTxt :=
      if la != lb then s!"(LeanCov.arm () >>= fun _ => (\n{spaces col}"
      else "(LeanCov.arm () >>= fun _ => ("
    acc.push { startPos := a.byteIdx, endPos := b.byteIdx, seq := acc.size + 1, openText := openTxt, closeText := "))" }
  | _, _ => acc

private partial def wrapMainEqns (fileMap : FileMap) (s : Syntax) (acc : Array Edit) : Array Edit :=
  match s with
  | .node _ `Lean.Parser.Term.matchAlt args =>
    if args.size ≥ 4 then wrapMainExpr fileMap args[3]! acc else acc
  | .node _ _ args => args.foldl (fun a c => wrapMainEqns fileMap c a) acc
  | _ => acc

private def collectMainDeclEdits (fileMap : FileMap) (cmd : Syntax) (ns : List String)
    (edits : Array Edit) : Array Edit := Id.run do
  unless cmd.getNumArgs ≥ 2 do return edits
  let inner := cmd.getArg 1
  unless inner.getKind == `Lean.Parser.Command.definition && inner.getNumArgs ≥ 4 do return edits
  let nm := declIdName (inner.getArg 1)
  unless (ns.isEmpty && nm == "main") || nm == "_root_.main" do return edits
  let valStx := inner.getArg 3
  match valStx.getKind with
  | `Lean.Parser.Command.declValSimple =>
    if valStx.getNumArgs ≥ 2 then wrapMainExpr fileMap (valStx.getArg 1) edits else edits
  | `Lean.Parser.Command.declValEqns =>
    wrapMainEqns fileMap valStx edits
  | _ => edits

private partial def collectMainArmEdits (fileMap : FileMap) (cmd : Syntax)
    (scopeStack : List (Bool × List String)) (ns : List String) (edits : Array Edit) :
    List (Bool × List String) × List String × Array Edit :=
  match stepScope? cmd scopeStack ns with
  | some (ss, ns') => (ss, ns', edits)
  | none =>
    match cmd.getKind with
    | `Lean.Parser.Command.in =>
      if cmd.getNumArgs ≥ 3 then collectMainArmEdits fileMap (cmd.getArg 2) scopeStack ns edits
      else (scopeStack, ns, edits)
    | `Lean.Parser.Command.declaration =>
      (scopeStack, ns, collectMainDeclEdits fileMap cmd ns edits)
    | _ => (scopeStack, ns, edits)

/-- Inject `LeanCov.arm ()` at entry to top-level `def main` so `LEAN_COV_DEFER_INIT=1` ignores
all probe hits fired during module initialization (`initialize_*`) before `main` begins. -/
def armMainInSource (env : Environment) (relFile src : String) : IO (String × Bool) := do
  if (src.splitOn "main").length ≤ 1 then return (src, false)
  let ic := mkInputContext src relFile
  let (hdr, pstate, msgs0) ← parseHeader ic
  if msgs0.hasErrors then return (src, false)
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut ps := pstate
  let mut msgs := msgs0
  let mut cmds : Array Syntax := #[]
  repeat
    let (cmd, ps', msgs') := parseCommand ic pmctx ps msgs
    ps := ps'
    msgs := msgs'
    if isTerminalCommand cmd then break
    cmds := cmds.push cmd
  if msgs.hasErrors then return (src, false)
  let mut scopeStack : List (Bool × List String) := []
  let mut ns : List String := []
  let mut edits : Array Edit := #[]
  for cmd in cmds do
    let (ss, ns', ed) := collectMainArmEdits ic.fileMap cmd scopeStack ns edits
    scopeStack := ss
    ns := ns'
    edits := ed
  if edits.isEmpty then return (src, false)
  let alreadyImports :=
    (src.splitOn "import LeanCov.DoSyntax").length > 1 ||
    (src.splitOn "import LeanCov.Runtime").length > 1
  let allEdits :=
    if alreadyImports then edits
    else
      let hdrEnd := (hdr.raw.getTailPos?.map (·.byteIdx)).getD 0
      let importLine :=
        if headerIsModule hdr.raw then
          if hdrEnd == 0 then "public import LeanCov.Runtime\n" else "\npublic import LeanCov.Runtime\n"
        else
          if hdrEnd == 0 then "import LeanCov.Runtime\n" else "\nimport LeanCov.Runtime\n"
      #[{ startPos := hdrEnd, endPos := hdrEnd, seq := 0, openText := importLine }] ++ edits
  return (applyEdits src allEdits, true)

/-- Recursively collect all `.lean` files under `dir`, sorted deterministically. -/
partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  if !(← dir.isDir) then return out
  for entry in (← dir.readDir) do
    let p := entry.path
    if ← p.isDir then
      let name := entry.fileName
      if name == ".lake" || name == ".git" || name == "build" then continue
      out := out ++ (← collectLeanFiles p)
    else if p.extension == some "lean" then
      out := out.push p
  return out.qsort fun a b => a.toString < b.toString

private def isExcluded (rel : String) (excludes : Array String) : Bool :=
  excludes.any fun pat => !pat.isEmpty && (rel.splitOn pat).length > 1

private def relativeTo (base file : System.FilePath) : String :=
  let b := base.toString
  let f := file.toString
  let pfx := if b.endsWith "/" then b else b ++ "/"
  if f.startsWith pfx then (f.drop pfx.length).toString else f

/-- Locate the Lean sysroot matching this `leancov` binary, even when invoked outside a project
directory with no `elan` default toolchain configured. -/
private def resolveSysroot : IO System.FilePath := do
  if let some sr ← IO.getEnv "LEAN_SYSROOT" then
    if !sr.isEmpty then return ⟨sr⟩
  -- Walk up from `leancov`'s own binary to find its `lean-toolchain` so `Init.olean` matches our build.
  let mut dir? := (← IO.appPath).parent
  for _ in [:8] do
    let some d := dir? | break
    if ← (d / "lean-toolchain").pathExists then
      let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := some d }
      if out.exitCode == 0 then
        let p := out.stdout.trimAscii.copy
        if !p.isEmpty then return ⟨p⟩
    dir? := d.parent
  findSysroot

/-- Build a Lean parser environment loading `Init` plus any extra syntax-providing modules. -/
unsafe def loadParserEnv (extraImports : Array Name := #[]) : IO Environment := do
  enableInitializersExecution
  initSearchPath (← resolveSysroot)
  let mods := #[{ module := `Init }] ++ extraImports.map fun m => { module := m }
  importModules mods {} (loadExts := true)

/-- Instrument all `.lean` files in `srcRoot` into `outRoot`, returning the combined `Manifest`.
When `armMains` is true, top-level `def main` entry points (even in excluded files) are armed
with `LeanCov.arm ()` so `LEAN_COV_DEFER_INIT=1` suppresses module-init probe hits. -/
unsafe def instrumentTree (srcRoot outRoot : System.FilePath) (cfg : InstrumentConfig := {})
    (startSiteId : Nat := 0) (relPrefix : String := "") (armMains : Bool := false) : IO Manifest := do
  let env ← loadParserEnv cfg.extraImports
  let files ← collectLeanFiles srcRoot
  let mut nextId := startSiteId
  let mut allSites : Array Site := #[]
  let mut allFuncs : Array FuncInfo := #[]
  let mut skipped : Array (String × String) := #[]
  let mut armedAny : Bool := false
  for f in files do
    let relLocal := relativeTo srcRoot f
    let relDisplay := if relPrefix.isEmpty then relLocal else s!"{relPrefix}/{relLocal}"
    let src ← IO.FS.readFile f
    let dest := outRoot / relLocal
    if isExcluded relDisplay cfg.exclude || isExcluded relLocal cfg.exclude then
      unless cfg.analyzeOnly do
        let (outSrc, armed) ← if armMains then armMainInSource env relDisplay src else pure (src, false)
        if armed then armedAny := true
        if let some p := dest.parent then IO.FS.createDirAll p
        IO.FS.writeFile dest outSrc
      continue
    let res ← instrumentSource env relDisplay src nextId cfg
    nextId := res.nextSiteId
    allSites := allSites ++ res.sites
    allFuncs := allFuncs ++ res.functions
    if let some why := res.skippedReason then
      skipped := skipped.push (relDisplay, why)
    unless cfg.analyzeOnly do
      let (outSrc, armed) ← if armMains then armMainInSource env relDisplay res.instrumented else pure (res.instrumented, false)
      if armed then armedAny := true
      if let some p := dest.parent then IO.FS.createDirAll p
      IO.FS.writeFile dest outSrc
  return { version := 1, armOnMain := armedAny, sites := allSites, functions := allFuncs, skippedFiles := skipped }

end LeanCov.Cov
