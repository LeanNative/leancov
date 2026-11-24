module

public import LeanCov.Runtime
public meta import Lean.Elab.Do

/-! # `do`-block and term coverage probe syntax (`leancov_hit%`, `leancov_term%`)

Both elaborators eagerly elaborate their wrapped expression/continuation before constructing
`LeanCov.hit` at the `Expr` level:
- exact `expectedType?` flows straight into `.ctor`, `⟨...⟩`, and numeric literals;
- exact metavariable unification order is preserved (preventing premature defaulting);
- `Prop` terms are silently left unwrapped so proofs never hit universe mismatches;
- `let mut`, `return`, `continue`, and `break` stay in scope in `do` blocks;
- LCNF never dead-code-eliminates probes, even in pure `Id.run do` blocks. -/

public section
syntax (name := doCovHit) "leancov_hit% " num : doElem
syntax (name := termCovHit) "leancov_term% " num term : term
end

private meta def wrapWithHit (n : Lean.TSyntax `num) (bodyExpr : Lean.Expr) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let bodyType ← Lean.Meta.inferType bodyExpr
  let bodyTypeWhnf ← Lean.Meta.whnf bodyType
  if (← Lean.Meta.isProp bodyExpr) || bodyType.isSort || bodyTypeWhnf.isSort then
    return bodyExpr
  let some u ← (try some <$> Lean.Meta.getDecLevel bodyType catch _ => pure none)
    | return bodyExpr
  let siteExpr ← Lean.Elab.Term.elabTerm (← `(($n : USize))) (some (Lean.mkConst ``USize))
  let thunk := Lean.mkLambda `_ .default (Lean.mkConst ``Unit) bodyExpr
  return Lean.mkApp3 (Lean.mkConst ``LeanCov.hit [u]) bodyType siteExpr thunk

@[doElem_control_info doCovHit]
public meta def controlInfoDoCovHit : Lean.Elab.Do.ControlInfoHandler := fun _ => pure .pure

@[doElem_elab doCovHit]
public meta def elabDoCovHit : Lean.Elab.Do.DoElab := fun stx dec => do
  let `(doCovHit| leancov_hit% $n:num) := stx | Lean.Elab.throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt stx
  let bodyExpr ← dec.continueWithUnit
  wrapWithHit n bodyExpr

@[term_elab termCovHit]
public meta def elabTermCovHit : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let `(termCovHit| leancov_term% $n:num $body) := stx | Lean.Elab.throwUnsupportedSyntax
  let bodyExpr ← Lean.Elab.Term.elabTermEnsuringType body expectedType?
  wrapWithHit n bodyExpr
