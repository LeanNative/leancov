import Lean

/-! # Syntax-based McCabe Cyclomatic Complexity and Cognitive Complexity

Computes both metrics directly from Lean's parsed `Syntax` tree (immune to comments, strings,
and token-splitting artifacts):

- **McCabe CC** (`cc`): `1` plus every branch point (`if`, `unless`, `for`, `while`, `repeat`,
  `catch`, `let … |`, `&&`, `||`, and each non-wildcard `match` / equation arm).
- **Cognitive Complexity** (`cognitive`): SonarSource-style nesting-weighted complexity:
  - `if`, `unless`, `for`, `while`, `repeat`, `catch`, `let … |`: `+ (1 + nesting)` and increases
    nesting for its body (`else if` adds `+1` flat without additional nesting penalty).
  - `match` / pattern-equation block: `+ (1 + nesting)` ONCE for the whole dispatch (not once per
    arm!), increasing nesting inside each arm. Flat Elm/TEA message routers therefore stay low
    while deeply nested stateful logic rises to the top.
  - `&&` / `||`: `+1` per boolean operator transition. -/

namespace LeanCov.Cov
open Lean

structure Complexity where
  cc : Nat := 1
  cognitive : Nat := 0
  deriving Repr, BEq, Inhabited

private partial def isWildcardPattern (s : Syntax) : Bool :=
  match s with
  | .node _ `Lean.Parser.Term.hole _ => true
  | .node _ `null args => !args.isEmpty && args.all isWildcardPattern
  | .atom _ "," => true
  | .atom _ "_" => true
  | _ => false

private partial def containsMatchAlts (s : Syntax) : Bool :=
  match s with
  | .node _ `Lean.Parser.Term.matchAlts _ => true
  | .node _ `Lean.Parser.Term.matchAltsWhereDecls _ => true
  | .node _ _ args => args.any containsMatchAlts
  | _ => false

private def skipKind (k : SyntaxNodeKind) : Bool :=
  k == `Lean.Parser.Term.byTactic ||
  k == `Lean.Parser.Term.typeSpec ||
  k == `Lean.Parser.Termination.suffix ||
  k == `Lean.Parser.Command.declModifiers

private structure WalkState where
  cc : Nat := 1
  cognitive : Nat := 0

private abbrev WalkM := StateM WalkState

private def addCC (n : Nat := 1) : WalkM Unit :=
  modify fun s => { s with cc := s.cc + n }

private def addCog (n : Nat) : WalkM Unit :=
  modify fun s => { s with cognitive := s.cognitive + n }

private partial def walk (stx : Syntax) (nesting : Nat) (lastBoolOp : Option Name := none) : WalkM Unit := do
  match stx with
  | .missing | .atom .. | .ident .. => pure ()
  | .node _ k args =>
    if skipKind k then return
    match k with
    | `termIfThenElse | `termDepIfThenElse | `termIfLet =>
      -- `if` / `else if`: detect chained `else if` on the else branch
      addCC 1
      addCog (1 + nesting)
      -- walk condition(s) at current nesting, then-branch at nesting+1, else-branch:
      -- if else-branch is another `termIf*`, treat it as `else if` (flat +1 cog instead of nesting)
      let n := args.size
      if n ≥ 6 then
        for i in [1 : n - 4] do walk args[i]! nesting none
        walk args[n - 3]! (nesting + 1) none
        let elseStx := args[n - 1]!
        if elseStx.getKind == `termIfThenElse || elseStx.getKind == `termDepIfThenElse || elseStx.getKind == `termIfLet then
          walkElseIf elseStx nesting
        else
          walk elseStx (nesting + 1) none
      else
        for a in args do walk a (nesting + 1) none
    | `Lean.Parser.Term.doIf =>
      -- #[atom("if"), cond, atom("then"), thenSeq, elseIfs, elseOpt]
      addCC 1
      addCog (1 + nesting)
      if args.size ≥ 6 then
        walk args[1]! nesting none
        walk args[3]! (nesting + 1) none
        for ei in args[4]!.getArgs do
          -- group #[group #[else, if], cond, then, seq]
          addCC 1
          addCog 1
          if ei.getNumArgs ≥ 4 then
            walk (ei.getArg 1) nesting none
            walk (ei.getArg 3) (nesting + 1) none
        let elseOpt := args[5]!
        if elseOpt.getNumArgs ≥ 2 then
          walk (elseOpt.getArg 1) (nesting + 1) none
      else
        for a in args do walk a (nesting + 1) none
    | `Lean.Parser.Term.doUnless =>
      addCC 1
      addCog (1 + nesting)
      if args.size ≥ 4 then
        walk args[1]! nesting none
        walk args[3]! (nesting + 1) none
    | `Lean.Parser.Term.doFor | `Lean.Parser.Term.doWhile | `Lean.Parser.Term.doRepeat =>
      addCC 1
      addCog (1 + nesting)
      for i in [:args.size] do
        if i + 1 == args.size then walk args[i]! (nesting + 1) none
        else walk args[i]! nesting none
    | `Lean.Parser.Term.doCatch =>
      addCC 1
      addCog (1 + nesting)
      if args.size > 0 then walk args[args.size - 1]! (nesting + 1) none
    | `Lean.Parser.Term.doLetElse =>
      -- #[let, mut?, letConfig, pat, :=, val, |, fallbackSeq, contOpt]
      addCC 1
      addCog (1 + nesting)
      if args.size ≥ 6 then walk args[5]! nesting none
      if args.size ≥ 8 then walk args[7]! (nesting + 1) none
      if args.size ≥ 9 then walk args[8]! nesting none
    | `Lean.Parser.Term.doPatDecl =>
      -- #[pat, typeSpecOpt, "←", val, fallbackOpt]
      if args.size ≥ 4 then walk args[3]! nesting none
      if args.size ≥ 5 then
        let fb := args[4]!
        if fb.getNumArgs ≥ 2 then
          addCC 1
          addCog (1 + nesting)
          walk (fb.getArg 1) (nesting + 1) none
          if fb.getNumArgs ≥ 3 then walk (fb.getArg 2) nesting none
    | `Lean.Parser.Term.match | `Lean.Parser.Term.doMatch | `Lean.Parser.Term.fun | `Lean.Parser.Command.declValEqns =>
      let hasAlts := containsMatchAlts stx
      if hasAlts then
        addCog (1 + nesting)
        walkMatchContainer stx (nesting + 1)
      else
        for a in args do walk a nesting none
    | `Lean.Parser.Term.matchAlt =>
      if args.size ≥ 4 then
        if !isWildcardPattern args[1]! then addCC 1
        walk args[3]! nesting none
    | `«term_&&_» | `«term_||_» =>
      addCC 1
      if lastBoolOp != some k then addCog 1
      if args.size ≥ 3 then
        walk args[0]! nesting (some k)
        walk args[2]! nesting (some k)
    | _ =>
      for a in args do walk a nesting none
where
  walkElseIf (stx : Syntax) (nesting : Nat) : WalkM Unit := do
    let args := stx.getArgs
    addCC 1
    addCog 1
    let n := args.size
    if n ≥ 6 then
      for i in [1 : n - 4] do walk args[i]! nesting none
      walk args[n - 3]! (nesting + 1) none
      let elseStx := args[n - 1]!
      if elseStx.getKind == `termIfThenElse || elseStx.getKind == `termDepIfThenElse || elseStx.getKind == `termIfLet then
        walkElseIf elseStx nesting
      else
        walk elseStx (nesting + 1) none
  walkMatchContainer (s : Syntax) (armNesting : Nat) : WalkM Unit := do
    match s with
    | .node _ `Lean.Parser.Term.matchAlt args =>
      if args.size ≥ 4 then
        if !isWildcardPattern args[1]! then addCC 1
        walk args[3]! armNesting none
    | .node _ k args =>
      if skipKind k then return
      if k == `Lean.Parser.Term.matchAlts || k == `Lean.Parser.Term.matchAltsWhereDecls || k == `null then
        for a in args do walkMatchContainer a armNesting
      else
        -- Discriminant or nested `where` declarations stay at outer nesting
        for a in args do
          if containsMatchAlts a then walkMatchContainer a armNesting
          else walk a (armNesting - 1) none
    | _ => pure ()

/-- Compute McCabe CC and Cognitive Complexity for a declaration value `Syntax` node. -/
def measureComplexity (valStx : Syntax) : Complexity :=
  let (_, s) := (walk valStx 0).run {}
  { cc := s.cc, cognitive := s.cognitive }

end LeanCov.Cov
