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

private def isTermIfKind (k : SyntaxNodeKind) : Bool :=
  k == `termIfThenElse || k == `termDepIfThenElse || k == `termIfLet

private def isMatchAltsGroup (k : SyntaxNodeKind) : Bool :=
  k == `Lean.Parser.Term.matchAlts || k == `Lean.Parser.Term.matchAltsWhereDecls || k == `null

private structure WalkState where
  cc : Nat := 1
  cognitive : Nat := 0

private abbrev WalkM := StateM WalkState

private def addCC (n : Nat := 1) : WalkM Unit :=
  modify fun s => { s with cc := s.cc + n }

private def addCog (n : Nat) : WalkM Unit :=
  modify fun s => { s with cognitive := s.cognitive + n }

mutual

private partial def walkTermIf (args : Array Syntax) (nesting : Nat) (isElseIf : Bool) : WalkM Unit := do
  -- `if` / `else if`: chained `else if` adds +1 flat without nesting penalty
  addCC 1
  addCog (if isElseIf then 1 else 1 + nesting)
  let n := args.size
  if n ≥ 6 then
    for i in [1 : n - 4] do walk args[i]! nesting none
    walk args[n - 3]! (nesting + 1) none
    let elseStx := args[n - 1]!
    if isTermIfKind elseStx.getKind then
      walkTermIf elseStx.getArgs nesting true
    else
      walk elseStx (nesting + 1) none
  else if !isElseIf then
    for a in args do walk a (nesting + 1) none

private partial def walkDoIf (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  -- #[atom("if"), cond, atom("then"), thenSeq, elseIfs, elseOpt]
  addCC 1
  addCog (1 + nesting)
  unless args.size ≥ 6 do
    for a in args do walk a (nesting + 1) none
    return
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

private partial def walkDoUnless (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  addCC 1
  addCog (1 + nesting)
  if args.size ≥ 4 then
    walk args[1]! nesting none
    walk args[3]! (nesting + 1) none

private partial def walkDoLoop (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  addCC 1
  addCog (1 + nesting)
  for i in [:args.size] do
    if i + 1 == args.size then walk args[i]! (nesting + 1) none
    else walk args[i]! nesting none

private partial def walkDoCatch (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  addCC 1
  addCog (1 + nesting)
  if args.size > 0 then walk args[args.size - 1]! (nesting + 1) none

private partial def walkDoLetElse (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  -- #[let, mut?, letConfig, pat, :=, val, |, fallbackSeq, contOpt]
  addCC 1
  addCog (1 + nesting)
  if args.size ≥ 6 then walk args[5]! nesting none
  if args.size ≥ 8 then walk args[7]! (nesting + 1) none
  if args.size ≥ 9 then walk args[8]! nesting none

private partial def walkDoPatDecl (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  -- #[pat, typeSpecOpt, "←", val, fallbackOpt]
  if args.size ≥ 4 then walk args[3]! nesting none
  unless args.size ≥ 5 do return
  let fb := args[4]!
  unless fb.getNumArgs ≥ 2 do return
  addCC 1
  addCog (1 + nesting)
  walk (fb.getArg 1) (nesting + 1) none
  if fb.getNumArgs ≥ 3 then walk (fb.getArg 2) nesting none

private partial def walkMatchAlt (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  if args.size ≥ 4 then
    if !isWildcardPattern args[1]! then addCC 1
    walk args[3]! nesting none

private partial def walkMatchContainer (s : Syntax) (armNesting : Nat) : WalkM Unit := do
  let .node _ k args := s | return
  if k == `Lean.Parser.Term.matchAlt then
    walkMatchAlt args armNesting
    return
  if skipKind k then return
  if isMatchAltsGroup k then
    for a in args do walkMatchContainer a armNesting
  else
    -- Discriminant or nested `where` declarations stay at outer nesting
    for a in args do
      if containsMatchAlts a then walkMatchContainer a armNesting
      else walk a (armNesting - 1) none

private partial def walkMatchOrEqns (stx : Syntax) (args : Array Syntax) (nesting : Nat) : WalkM Unit := do
  if containsMatchAlts stx then
    addCog (1 + nesting)
    walkMatchContainer stx (nesting + 1)
  else
    for a in args do walk a nesting none

private partial def walkBoolOp (k : SyntaxNodeKind) (args : Array Syntax) (nesting : Nat)
    (lastBoolOp : Option Name) : WalkM Unit := do
  addCC 1
  if lastBoolOp != some k then addCog 1
  if args.size ≥ 3 then
    walk args[0]! nesting (some k)
    walk args[2]! nesting (some k)

private partial def walk (stx : Syntax) (nesting : Nat) (lastBoolOp : Option Name := none) : WalkM Unit := do
  let .node _ k args := stx | return
  if skipKind k then return
  match k with
  | `termIfThenElse | `termDepIfThenElse | `termIfLet =>
    walkTermIf args nesting false
  | `Lean.Parser.Term.doIf =>
    walkDoIf args nesting
  | `Lean.Parser.Term.doUnless =>
    walkDoUnless args nesting
  | `Lean.Parser.Term.doFor | `Lean.Parser.Term.doWhile | `Lean.Parser.Term.doRepeat =>
    walkDoLoop args nesting
  | `Lean.Parser.Term.doCatch =>
    walkDoCatch args nesting
  | `Lean.Parser.Term.doLetElse =>
    walkDoLetElse args nesting
  | `Lean.Parser.Term.doPatDecl =>
    walkDoPatDecl args nesting
  | `Lean.Parser.Term.match | `Lean.Parser.Term.doMatch | `Lean.Parser.Term.fun | `Lean.Parser.Command.declValEqns =>
    walkMatchOrEqns stx args nesting
  | `Lean.Parser.Term.matchAlt =>
    walkMatchAlt args nesting
  | `«term_&&_» | `«term_||_» =>
    walkBoolOp k args nesting lastBoolOp
  | _ =>
    for a in args do walk a nesting none

end

/-- Compute McCabe CC and Cognitive Complexity for a declaration value `Syntax` node. -/
def measureComplexity (valStx : Syntax) : Complexity :=
  let (_, s) := (walk valStx 0).run {}
  { cc := s.cc, cognitive := s.cognitive }

end LeanCov.Cov
