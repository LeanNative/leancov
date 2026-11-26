import Lean
import Lean.Data.Json
import Std.Data.HashMap
import LeanCov.Cov.Types
import LeanCov.Cov.Instrument

/-! # AST-Guided Source Mutator & Mutation Testing Engine

Discovers syntax-valid, semantics-altering mutants inside computational Lean 4 declarations
using `loadParserEnv` + exact UTF-8 byte spans, then evaluates each mutant in an isolated
staged Lake workspace with wall-clock timeouts. -/

namespace LeanCov.Cov
open Lean Parser

/-- Category of AST source mutation. -/
inductive MutantKind where
  | cmpFlip
  | arithFlip
  | boolOpFlip
  | boolLitFlip
  | negRemove
  | condNegate
  deriving Repr, BEq, Inhabited

def MutantKind.toString : MutantKind → String
  | .cmpFlip => "cmp.flip"
  | .arithFlip => "arith.flip"
  | .boolOpFlip => "bool.op"
  | .boolLitFlip => "bool.lit"
  | .negRemove => "neg.remove"
  | .condNegate => "cond.negate"

def MutantKind.ofString? : String → Option MutantKind
  | "cmp.flip" => some .cmpFlip
  | "arith.flip" => some .arithFlip
  | "bool.op" => some .boolOpFlip
  | "bool.lit" => some .boolLitFlip
  | "neg.remove" => some .negRemove
  | "cond.negate" => some .condNegate
  | _ => none

instance : ToJson MutantKind := ⟨fun k => Json.str k.toString⟩
instance : FromJson MutantKind where
  fromJson? j := do
    let s ← j.getStr?
    match MutantKind.ofString? s with
    | some k => pure k
    | none => throw s!"unknown mutant kind: {s}"

/-- Outcome of compiling and running proofs/tests against one mutant. -/
inductive MutantOutcome where
  | killed
  | proved
  | survived
  | timeout
  | uncompilable
  | uncovered
  deriving Repr, BEq, Inhabited

def MutantOutcome.toString : MutantOutcome → String
  | .killed => "killed"
  | .proved => "proved"
  | .survived => "survived"
  | .timeout => "timeout"
  | .uncompilable => "uncompilable"
  | .uncovered => "uncovered"

def MutantOutcome.ofString? : String → Option MutantOutcome
  | "killed" => some .killed
  | "proved" => some .proved
  | "survived" => some .survived
  | "timeout" => some .timeout
  | "uncompilable" => some .uncompilable
  | "uncovered" => some .uncovered
  | _ => none

instance : ToJson MutantOutcome := ⟨fun o => Json.str o.toString⟩
instance : FromJson MutantOutcome where
  fromJson? j := do
    let s ← j.getStr?
    match MutantOutcome.ofString? s with
    | some o => pure o
    | none => throw s!"unknown mutant outcome: {s}"

/-- A single source-level mutation candidate. -/
structure Mutant where
  id : Nat
  file : String
  decl : String
  line : Nat
  col : Nat
  kind : MutantKind
  original : String
  replacement : String
  startByte : Nat
  endByte : Nat
  repText : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Execution result for one mutant. -/
structure MutantResult where
  mutant : Mutant
  outcome : MutantOutcome
  elapsedMs : Nat := 0
  deriving Repr, Inhabited, ToJson, FromJson

/-- Aggregated summary across a mutation testing run. -/
structure MutateReport where
  discovered : Nat
  generated : Nat
  uncompilable : Nat
  uncovered : Nat := 0
  tested : Nat
  killed : Nat
  proved : Nat := 0
  timeout : Nat
  survived : Nat
  score : Float
  results : Array MutantResult
  deriving Repr, Inhabited, ToJson

/-- Splice a single `Mutant` into UTF-8 source text. -/
def applyMutant (src : String) (m : Mutant) : String :=
  let bytes := src.toUTF8
  let s := min m.startByte bytes.size
  let e := min (max s m.endByte) bytes.size
  String.fromUTF8! (bytes.extract 0 s ++ m.repText.toUTF8 ++ bytes.extract e bytes.size)

private def cmpFlip? : String → Option String
  | "==" => some "!="
  | "!=" => some "=="
  | "<"  => some "≤"
  | "≤"  => some "<"
  | "<=" => some "<"
  | ">"  => some "≥"
  | "≥"  => some ">"
  | ">=" => some ">"
  | _    => none

private def arithFlip? : String → Option String
  | "+"   => some "-"
  | "-"   => some "+"
  | "*"   => some "/"
  | "/"   => some "*"
  | "&&&" => some "|||"
  | "|||" => some "&&&"
  | "<<<" => some ">>>"
  | ">>>" => some "<<<"
  | _     => none

private def boolOpFlip? : String → Option String
  | "&&" => some "||"
  | "||" => some "&&"
  | _    => none

private def boolLitFlip? : String → Option String
  | "true"       => some "false"
  | "false"      => some "true"
  | "Bool.true"  => some "Bool.false"
  | "Bool.false" => some "Bool.true"
  | _            => none

private def compactDisp (s : String) : String :=
  let flat := (s.replace "\n" " ").trimAscii.copy
  if flat.length ≤ 40 then flat else String.ofList (flat.toList.take 37) ++ "..."

private structure MutState where
  file : String
  src : String
  bytes : ByteArray
  fileMap : FileMap
  nextId : Nat
  decl : String := ""
  includeArith : Bool := true
  includeInterp : Bool := false
  ignoredLines : Std.HashMap Nat Bool := {}
  mutants : Array Mutant := #[]

private abbrev MutM := StateM MutState

private def computeMutantIgnoredLines (src : String) : Std.HashMap Nat Bool := Id.run do
  let mut out := computeIgnoredLines src "leancov:ignore"
  for (ln, _) in (computeIgnoredLines src "leancov:ignore-mutant").toList do
    out := out.insert ln true
  return out

private def sliceBytes (s : MutState) (a b : String.Pos.Raw) : String :=
  String.fromUTF8! (s.bytes.extract a.byteIdx (min b.byteIdx s.bytes.size))

private def recordMutant (pos tailPos : String.Pos.Raw) (kind : MutantKind)
    (origDisp repDisp repText : String) : MutM Unit := do
  let s ← get
  let p := s.fileMap.toPosition pos
  if s.ignoredLines.contains p.line then return
  let m : Mutant := {
    id := s.nextId
    file := s.file
    decl := s.decl
    line := p.line
    col := p.column + 1
    kind := kind
    original := origDisp
    replacement := repDisp
    startByte := pos.byteIdx
    endByte := tailPos.byteIdx
    repText := repText
  }
  set { s with nextId := s.nextId + 1, mutants := s.mutants.push m }

private def emitInfixFlip (opAtom : Syntax) (kind : MutantKind) (flip? : String → Option String) : MutM Unit := do
  let s ← get
  if let (some a, some b) := (opAtom.getPos?, opAtom.getTailPos?) then
    let orig := sliceBytes s a b
    if let some rep := flip? orig then
      recordMutant a b kind orig rep rep

private def emitNegRemove (stx inner : Syntax) : MutM Unit := do
  let s ← get
  if let (some a, some b, some ia, some ib) := (stx.getPos?, stx.getTailPos?, inner.getPos?, inner.getTailPos?) then
    let origTxt := sliceBytes s a b
    let innerTxt := sliceBytes s ia ib
    let repTxt :=
      if inner.isIdent || inner.getKind == `Lean.Parser.Term.paren then innerTxt
      else s!"({innerTxt})"
    recordMutant a b .negRemove (compactDisp origTxt) (compactDisp repTxt) repTxt

private def redundantOrPropCondKinds : Array SyntaxNodeKind := #[
  `term!_, `«term_==_», `«term_!=_»,
  `«term_=_», `«term_≠_», `«term_¬_», `«term_∧_», `«term_∨_», `«term_∈_», `«term_∉_»
]

private def isRedundantOrPropCond (u : Syntax) (s : MutState) : Bool :=
  if redundantOrPropCondKinds.contains u.getKind then
    true
  else if u.isIdent then
    match u.getPos?, u.getTailPos? with
    | some a, some b => (boolLitFlip? (sliceBytes s a b)).isSome
    | _, _ => false
  else false

private def maybeNegateCond (cond : Syntax) : MutM Unit := do
  let s ← get
  let u := unwrapParen cond
  if isRedundantOrPropCond u s then return
  if let (some a, some b) := (cond.getPos?, cond.getTailPos?) then
    let condTxt := sliceBytes s a b
    let pa := s.fileMap.toPosition a
    let pb := s.fileMap.toPosition b
    let repTxt :=
      if pa.line == pb.line then s!"!({condTxt})"
      else
        let ind := String.ofList (List.replicate pa.column ' ')
        s!"!(\n{ind}{condTxt})"
    let disp := compactDisp condTxt
    recordMutant a b .condNegate disp s!"!({disp})" repTxt

private def cmpKinds : Array SyntaxNodeKind := #[
  `«term_==_», `«term_!=_», `«term_<_», `«term_≤_», `«term_>_», `«term_≥_»
]

private def arithKinds : Array SyntaxNodeKind := #[
  `«term_+_», `«term_-_», `«term_*_», `«term_/_»,
  `«term_&&&_», `«term_|||_», `«term_<<<_», `«term_>>>_»
]

private def isCmpKind (k : SyntaxNodeKind) : Bool :=
  cmpKinds.contains k

private def isArithKind (k : SyntaxNodeKind) : Bool :=
  arithKinds.contains k

private def skippedMutNodeKinds : Array SyntaxNodeKind := #[
  `Lean.Parser.Term.dotIdent, `Lean.Parser.Term.structInstLVal
]

mutual

private partial def walkMutAt (args : Array Syntax) (idx : Nat) : MutM Unit := do
  if idx < args.size then walkMutExpr args[idx]!

private partial def walkDoIfCond (cNode : Syntax) : MutM Unit := do
  let k := cNode.getKind
  if k == `Lean.Parser.Term.doIfProp && cNode.getNumArgs ≥ 2 then
    let hasBinder := (cNode.getArg 0).getNumArgs > 0
    let cond := cNode.getArg 1
    if !hasBinder then maybeNegateCond cond
    walkMutExpr cond
  else if k == `Lean.Parser.Term.doIfLet && cNode.getNumArgs ≥ 3 then
    walkMutExpr (cNode.getArg 2)
  else
    walkMutExpr cNode

private partial def walkMutDoIf (args : Array Syntax) : MutM Unit := do
  unless args.size ≥ 6 do
    for a in args do walkMutExpr a
    return
  walkDoIfCond args[1]!
  walkMutExpr args[3]!
  for ei in args[4]!.getArgs do
    if ei.getNumArgs ≥ 4 then
      walkDoIfCond (ei.getArg 1)
      walkMutExpr (ei.getArg 3)
  if args[5]!.getNumArgs ≥ 2 then
    walkMutExpr (args[5]!.getArg 1)

private partial def walkMutDoPatDecl (args : Array Syntax) : MutM Unit := do
  walkMutAt args 3
  if args.size ≥ 5 then
    let fb := args[4]!
    if fb.getNumArgs ≥ 2 then walkMutExpr (fb.getArg 1)
    if fb.getNumArgs ≥ 3 then walkMutExpr (fb.getArg 2)

private partial def walkMutOp? (stx : Syntax) (k : SyntaxNodeKind) (args : Array Syntax) : MutM Bool := do
  if isCmpKind k && args.size ≥ 3 then
    emitInfixFlip args[1]! .cmpFlip cmpFlip?
    walkMutExpr args[0]!; walkMutExpr args[2]!
    return true
  if isArithKind k && args.size ≥ 3 then
    if (← get).includeArith then
      emitInfixFlip args[1]! .arithFlip arithFlip?
    walkMutExpr args[0]!; walkMutExpr args[2]!
    return true
  if (k == `«term_&&_» || k == `«term_||_») && args.size ≥ 3 then
    emitInfixFlip args[1]! .boolOpFlip boolOpFlip?
    walkMutExpr args[0]!; walkMutExpr args[2]!
    return true
  if k == `term!_ && args.size ≥ 2 then
    emitNegRemove stx args[1]!
    walkMutExpr args[1]!
    return true
  return false

private partial def walkMutIfOrUnless? (k : SyntaxNodeKind) (args : Array Syntax) : MutM Bool := do
  match k with
  | `termIfThenElse =>
    if args.size ≥ 6 then
      maybeNegateCond args[1]!
      walkMutExpr args[1]!; walkMutExpr args[3]!; walkMutExpr args[5]!
    else for a in args do walkMutExpr a
    return true
  | `termDepIfThenElse =>
    let n := args.size
    if n ≥ 6 then walkMutExpr args[n - 5]!; walkMutExpr args[n - 3]!; walkMutExpr args[n - 1]!
    return true
  | `termIfLet =>
    if args.size ≥ 9 then walkMutExpr args[4]!; walkMutExpr args[6]!; walkMutExpr args[8]!
    return true
  | `Lean.Parser.Term.doIf =>
    walkMutDoIf args
    return true
  | `Lean.Parser.Term.doUnless =>
    if args.size ≥ 4 then
      maybeNegateCond args[1]!
      walkMutExpr args[1]!; walkMutExpr args[3]!
    return true
  | _ => return false

private partial def walkMutNode (stx : Syntax) (k : SyntaxNodeKind) (args : Array Syntax) : MutM Unit := do
  if skipWalkKind k || skippedMutNodeKinds.contains k then return
  if k == `interpolatedStrKind && !(← get).includeInterp then return
  if ← walkMutOp? stx k args then return
  if ← walkMutIfOrUnless? k args then return
  match k with
  | `Lean.Parser.Term.typeAscription => walkMutAt args 1
  | `Lean.Parser.Term.proj => walkMutAt args 0
  | `Lean.Parser.Term.matchAlt => walkMutAt args 3
  | `Lean.Parser.Term.letIdDecl | `Lean.Parser.Term.letPatDecl => walkMutAt args 4
  | `Lean.Parser.Term.doIdDecl => walkMutAt args 3
  | `Lean.Parser.Term.doPatDecl => walkMutDoPatDecl args
  | `Lean.Parser.Term.doLetElse => walkMutAt args 5; walkMutAt args 7; walkMutAt args 8
  | `Lean.Parser.Term.doForDecl => if args.size > 0 then walkMutAt args (args.size - 1)
  | `Lean.Parser.Term.structInstField => if args.size ≥ 2 then walkMutAt args (args.size - 1)
  | _ => for a in args do walkMutExpr a

private partial def walkMutExpr (stx : Syntax) : MutM Unit := do
  match stx with
  | .ident _ _ _ _ =>
    let s ← get
    if let (some a, some b) := (stx.getPos?, stx.getTailPos?) then
      let txt := sliceBytes s a b
      if let some rep := boolLitFlip? txt then
        recordMutant a b .boolLitFlip txt rep rep
  | .node _ k args => walkMutNode stx k args
  | _ => pure ()

end

private def matchesDeclFilter (filters : Array String) (rawName qname : String) : Bool :=
  filters.isEmpty || filters.any fun pat =>
    !pat.isEmpty && ((qname.splitOn pat).length > 1 || (rawName.splitOn pat).length > 1)

private def mutateDecl (ns : List String) (filters : Array String) (mods inner : Syntax) : MutM Unit := do
  let s ← get
  if shouldSkipModifiers mods s.src then return
  let some (rawName, sigStx, valStx) := extractDeclHead? inner s.src (allowAbbrev := true) | return
  if isNonComputationalSig sigStx s.src then return
  if isTacticBody valStx then return
  let qname := qualifyName ns rawName
  unless matchesDeclFilter filters rawName qname do return
  modify fun st => { st with decl := qname }
  match valStx.getKind with
  | `Lean.Parser.Command.declValSimple =>
    if valStx.getNumArgs ≥ 2 then walkMutExpr (valStx.getArg 1)
    if valStx.getNumArgs ≥ 4 then walkMutExpr (valStx.getArg 3)
  | `Lean.Parser.Command.declValEqns | `Lean.Parser.Command.whereStructInst =>
    walkMutExpr valStx
  | _ => pure ()

private partial def walkMutCommand (cmd : Syntax) (scopeStack : List (Bool × List String))
    (ns : List String) (filters : Array String) : MutM (List (Bool × List String) × List String) := do
  if let some (ss, ns') := stepScope? cmd scopeStack ns then
    return (ss, ns')
  match cmd.getKind with
  | `Lean.Parser.Command.in =>
    if cmd.getNumArgs ≥ 3 then walkMutCommand (cmd.getArg 2) scopeStack ns filters
    else return (scopeStack, ns)
  | `Lean.Parser.Command.mutual =>
    if cmd.getNumArgs ≥ 2 then
      for d in (cmd.getArg 1).getArgs do
        let _ ← walkMutCommand d scopeStack ns filters
    return (scopeStack, ns)
  | `Lean.Parser.Command.declaration =>
    if cmd.getNumArgs ≥ 2 then
      mutateDecl ns filters (cmd.getArg 0) (cmd.getArg 1)
    return (scopeStack, ns)
  | _ => return (scopeStack, ns)

/-- Parse a `.lean` source file and return all AST-guided mutants in computational declarations. -/
def discoverMutantsInSource (env : Environment) (relFile src : String) (startId : Nat := 0)
    (filters : Array String := #[]) (includeArith : Bool := true)
    (includeInterp : Bool := false) : IO (Array Mutant) := do
  let ic := mkInputContext src relFile
  let (_, pstate, msgs0) ← parseHeader ic
  if msgs0.hasErrors then return #[]
  let pmctx : ParserModuleContext := { env, options := {} }
  let (cmds, _) ← parseCommandsResilient ic pmctx pstate
  let init : MutState := {
    file := relFile, src, bytes := src.toUTF8, fileMap := ic.fileMap, nextId := startId,
    includeArith := includeArith,
    includeInterp := includeInterp,
    ignoredLines := computeMutantIgnoredLines src
  }
  let run : MutM Unit := do
    let mut scopeStack : List (Bool × List String) := []
    let mut ns : List String := []
    for (cmd, hasErr) in cmds do
      if hasErr then
        if let some (ss, ns') := stepScope? cmd scopeStack ns then
          scopeStack := ss
          ns := ns'
      else
        let (ss, ns') ← walkMutCommand cmd scopeStack ns filters
        scopeStack := ss
        ns := ns'
  let (_, st) := run.run init
  return st.mutants

/-! ## Subprocess execution with wall-clock timeout -/

inductive ExecStatus where
  | exited (code : UInt32) (elapsedMs : Nat)
  | timedOut (elapsedMs : Nat)

/-- Spawn `cmd args` in `cwd` with `/dev/null` stdio and enforce a wall-clock timeout in ms. -/
def runWithTimeout (cmd : String) (args : Array String) (cwd : System.FilePath)
    (timeoutMs : Nat) : IO ExecStatus := do
  let t0 ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := some cwd
    stdin := .null
    stdout := .null
    stderr := .null
  }
  repeat
    if let some code ← child.tryWait then
      return .exited code ((← IO.monoMsNow) - t0)
    let elapsed := (← IO.monoMsNow) - t0
    if elapsed ≥ timeoutMs then
      try child.kill catch _ => pure ()
      let _ ← try child.wait catch _ => pure 137
      return .timedOut elapsed
    IO.sleep 15
  return .timedOut timeoutMs

/-- Configuration for running a mutation campaign inside an already-staged `workDir`. -/
structure MutateRunConfig where
  workDir : System.FilePath
  buildTargets : Array String := #[]
  proofTargets : Array String := #[]
  noBuild : Bool := false
  testCmd : String
  testArgs : Array String := #[]
  timeoutMs : Nat := 30000

private def runLakeBuildTargets (workDir : System.FilePath) (targets : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["build"] ++ targets
    cwd := some workDir
  }
  return (out.exitCode, out.stdout ++ out.stderr)

private def buildWorkspace (cfg : MutateRunConfig) : IO (UInt32 × String) := do
  if cfg.noBuild then return (0, "")
  runLakeBuildTargets cfg.workDir cfg.buildTargets

private def buildProofTargets (cfg : MutateRunConfig) : IO (UInt32 × String) := do
  if cfg.proofTargets.isEmpty then return (0, "")
  runLakeBuildTargets cfg.workDir cfg.proofTargets

private def pathMatchesMutFile (mutFile otherFile : String) : Bool :=
  mutFile == otherFile || otherFile.endsWith ("/" ++ mutFile) || mutFile.endsWith ("/" ++ otherFile)

private def siteHitAt (hits : Array UInt64) (id : Nat) : UInt64 :=
  if h : id < hits.size then hits[id] else 0

/-- Filter mutants to those whose source line was modified/added in a parsed git diff. -/
def filterMutantsByGitDiff (ms : Array Mutant) (changedLines : Std.HashMap String (Array Nat)) : Array Mutant :=
  let entries := changedLines.toArray.map fun (f, lns) =>
    let mp := lns.foldl (fun (acc : Std.HashMap Nat Bool) ln => acc.insert ln true) {}
    (f, mp)
  let kept := ms.filter fun m =>
    entries.any fun (df, mp) => pathMatchesMutFile m.file df && mp.contains m.line
  kept.mapIdx fun i m => { m with id := i }

private def splitMixNext (st : UInt64) : UInt64 × UInt64 :=
  let s := st + 0x9E3779B97F4A7C15
  let a := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let b := (a ^^^ (a >>> 27)) * 0x94D049BB133111EB
  (s, b ^^^ (b >>> 31))

/-- Select up to `maxN` mutants, optionally using a deterministic SplitMix64 shuffle when `seed?` is set. -/
def sampleMutants (ms : Array Mutant) (maxN : Nat) (seed? : Option UInt64) : Array Mutant := Id.run do
  let ordered := match seed? with
    | none => ms
    | some seed => Id.run do
      let mut arr := ms
      let mut st := seed
      let n := arr.size
      if n > 1 then
        for i in [:n - 1] do
          let (st', rnd) := splitMixNext st
          st := st'
          let j := i + (rnd.toNat % (n - i))
          let tmp := arr[i]!
          arr := arr.set! i arr[j]!
          arr := arr.set! j tmp
      arr
  (ordered.take maxN).mapIdx fun i m => { m with id := i }

/-- Prune mutants whose line (or enclosing function) had 0 runtime coverage hits, marking them `.uncovered`. -/
def pruneUncoveredMutants (mutants : Array Mutant) (m : Manifest) (hits : Array UInt64) :
    Array Mutant × Array MutantResult := Id.run do
  let mut toTest : Array Mutant := #[]
  let mut pruned : Array MutantResult := #[]
  for mt in mutants do
    let lineSites := m.sites.filter fun s => pathMatchesMutFile mt.file s.file && s.line == mt.line
    let isUncov :=
      if !lineSites.isEmpty then
        lineSites.all fun s => siteHitAt hits s.id == 0
      else
        match m.functions.find? fun f => f.name == mt.decl && pathMatchesMutFile mt.file f.file with
        | some fn => !fn.siteIds.isEmpty && fn.siteIds.all fun sid => siteHitAt hits sid == 0
        | none => false
    if isUncov then
      pruned := pruned.push { mutant := mt, outcome := .uncovered, elapsedMs := 0 }
    else
      toTest := toTest.push mt
  (toTest.mapIdx fun i mt => { mt with id := i }, pruned)

private def evalOneMutant (cfg : MutateRunConfig) (origSrc : String) (m : Mutant) : IO MutantResult := do
  let targetPath := cfg.workDir / m.file
  IO.FS.writeFile targetPath (applyMutant origSrc m)
  try
    let t0 ← IO.monoMsNow
    let (bCode, _) ← buildWorkspace cfg
    if bCode != 0 then
      let elapsed := (← IO.monoMsNow) - t0
      IO.FS.writeFile targetPath origSrc
      return { mutant := m, outcome := .uncompilable, elapsedMs := elapsed }
    let (pCode, _) ← buildProofTargets cfg
    if pCode != 0 then
      let elapsed := (← IO.monoMsNow) - t0
      IO.FS.writeFile targetPath origSrc
      return { mutant := m, outcome := .proved, elapsedMs := elapsed }
    let status ← runWithTimeout cfg.testCmd cfg.testArgs cfg.workDir cfg.timeoutMs
    IO.FS.writeFile targetPath origSrc
    match status with
    | .timedOut ms => return { mutant := m, outcome := .timeout, elapsedMs := ms }
    | .exited code ms =>
      let out := if code != 0 then MutantOutcome.killed else .survived
      return { mutant := m, outcome := out, elapsedMs := ms }
  catch e =>
    try IO.FS.writeFile targetPath origSrc catch _ => pure ()
    throw e

/-- Build aggregate `MutateReport` from raw `MutantResult` records. -/
def summarizeMutateResults (discovered : Nat) (results : Array MutantResult) : MutateReport := Id.run do
  let mut uncompilable := 0
  let mut uncovered := 0
  let mut killed := 0
  let mut proved := 0
  let mut timeout := 0
  let mut survived := 0
  for r in results do
    match r.outcome with
    | .uncompilable => uncompilable := uncompilable + 1
    | .uncovered => uncovered := uncovered + 1
    | .killed => killed := killed + 1
    | .proved => proved := proved + 1
    | .timeout => timeout := timeout + 1
    | .survived => survived := survived + 1
  let tested := proved + killed + timeout + survived
  let score := if tested == 0 then 100.0 else 100.0 * Float.ofNat (proved + killed + timeout) / Float.ofNat tested
  return {
    discovered
    generated := results.size
    uncompilable, uncovered, tested, killed, proved, timeout, survived
    score, results
  }

/-- Execute baseline verification (`lake build`, proof targets, and `testCmd`) and evaluate every mutant in `selected`. -/
def executeMutants (cfg : MutateRunConfig) (origByFile : Std.HashMap String String)
    (discovered : Nat) (selected : Array Mutant)
    (resolveCmd : IO (Except String String))
    (preResults : Array MutantResult := #[]) : IO (Except String MutateReport) := do
  let (baseBuildCode, baseBuildLog) ← buildWorkspace cfg
  if baseBuildCode != 0 then
    return .error s!"mutate: baseline `lake build` failed (exit {baseBuildCode}):\n{baseBuildLog}"
  let (baseProofCode, baseProofLog) ← buildProofTargets cfg
  if baseProofCode != 0 then
    return .error s!"mutate: baseline proof `lake build` failed (exit {baseProofCode}):\n{baseProofLog}"
  let resolvedCmd ← match ← resolveCmd with
    | .ok c => pure c
    | .error e => return .error e
  let runCfg := { cfg with testCmd := resolvedCmd }
  match ← runWithTimeout runCfg.testCmd runCfg.testArgs runCfg.workDir runCfg.timeoutMs with
  | .timedOut ms =>
    return .error s!"mutate: baseline test command timed out after {ms}ms"
  | .exited code _ =>
    if code != 0 then
      return .error s!"mutate: baseline test command failed with exit code {code} before any mutation"
  let mut results : Array MutantResult := preResults
  for i in [:selected.size] do
    let m := selected[i]!
    let origSrc := origByFile.getD m.file ""
    let res ← evalOneMutant runCfg origSrc m
    let tag := match res.outcome with
      | .killed => "KILLED      "
      | .proved => "PROVED      "
      | .survived => "SURVIVED    "
      | .timeout => "TIMEOUT     "
      | .uncompilable => "UNCOMPILABLE"
      | .uncovered => "UNCOVERED   "
    IO.println s!"  [{i + 1}/{selected.size}] {tag} {m.file}:{m.line} ({m.decl}) `{m.original}` -> `{m.replacement}` ({res.elapsedMs}ms)"
    results := results.push res
  return .ok (summarizeMutateResults discovered results)

private def round1Mut (x : Float) : String :=
  let scaled := (x * 10.0 + 0.5).toUInt64.toNat
  s!"{scaled / 10}.{scaled % 10}"

/-- Format a human-readable mutation testing summary, listing every `SURVIVED` mutant. -/
def formatMutateReport (r : MutateReport) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "=== LeanCov AST Mutation Report ==="
  let capNote := if r.discovered > r.generated then s!" (sampled from {r.discovered} discovered)" else ""
  out := out.push s!"Generated:    {r.generated}{capNote}"
  let uncovNote := if r.uncovered > 0 then s!" | Uncovered: {r.uncovered}" else ""
  out := out.push s!"Uncompilable: {r.uncompilable}{uncovNote} (excluded from denominator)"
  let provedNote := if r.proved > 0 then s!"Proved: {r.proved} | " else ""
  out := out.push s!"Tested:       {r.tested} | {provedNote}Killed: {r.killed} | Timeout: {r.timeout} | Survived: {r.survived}"
  out := out.push s!"Score:        {round1Mut r.score}% ({r.proved + r.killed + r.timeout}/{r.tested})"
  let survivors := r.results.filter (·.outcome == .survived)
  if !survivors.isEmpty then
    out := out.push ""
    out := out.push s!"Survived mutants ({survivors.size}):"
    for sr in survivors do
      let m := sr.mutant
      out := out.push s!"  SURVIVED {m.file}:{m.line}:{m.col}  {m.decl}  [{m.kind.toString}] `{m.original}` -> `{m.replacement}`"
  return "\n".intercalate out.toList

/-- Format a mutation testing summary as GitHub-flavored Markdown. -/
def formatMutateMarkdown (r : MutateReport) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push "## LeanCov Mutation Report"
  out := out.push ""
  out := out.push "| Metric | Value |"
  out := out.push "|---|---:|"
  let capNote := if r.discovered > r.generated then s!" (sampled from {r.discovered})" else ""
  out := out.push s!"| Generated | {r.generated}{capNote} |"
  out := out.push s!"| Tested | {r.tested} |"
  out := out.push s!"| Proved | {r.proved} |"
  out := out.push s!"| Killed | {r.killed} |"
  out := out.push s!"| Timeout | {r.timeout} |"
  out := out.push s!"| Survived | {r.survived} |"
  out := out.push s!"| Uncompilable | {r.uncompilable} |"
  out := out.push s!"| Uncovered | {r.uncovered} |"
  out := out.push s!"| Mutation Score | {round1Mut r.score}% |"
  let survivors := r.results.filter (·.outcome == .survived)
  if !survivors.isEmpty then
    out := out.push ""
    out := out.push s!"### Survived Mutants ({survivors.size})"
    out := out.push ""
    out := out.push "| Location | Declaration | Kind | Mutation |"
    out := out.push "|---|---|---|---|"
    for sr in survivors do
      let m := sr.mutant
      out := out.push s!"| `{m.file}:{m.line}:{m.col}` | `{m.decl}` | `{m.kind.toString}` | `{m.original}` -> `{m.replacement}` |"
  return "\n".intercalate out.toList ++ "\n"

end LeanCov.Cov
