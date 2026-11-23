module

/-! # Minimal runtime probes for LeanCov source-level instrumentation

Zero `Lean` imports: safe to link into any runtime or test binary. When `LEAN_COV_FILE` is unset,
each probe is a single null-pointer check; when set, each hit atomically increments its 64-bit
counter in a `MAP_SHARED` file so counts survive crashes and `SIGKILL`. -/

namespace LeanCov

/-- Enables coverage recording on entry to `main` (ignoring hits from module initializers when
`LEAN_COV_DEFER_INIT=1`). -/
@[extern "leancov_arm", noinline, never_extract]
public def arm (_ : Unit) : IO Unit := pure ()

/-- Records a hit on `site`, then evaluates and returns `f ()`. -/
@[extern "leancov_hit", noinline, never_extract]
public def hit {α : Type u} (_site : USize) (f : Unit → α) : α := f ()

/-- Records a hit on `tSite` if `b` is true or `fSite` if false, returning `b` unchanged. -/
@[extern "leancov_cond", noinline, never_extract]
public def cond (_tSite _fSite : USize) (b : Bool) : Bool := b

/-- Records a hit on `site` and returns `x` unchanged. -/
@[extern "leancov_pass", noinline, never_extract]
public def pass {α : Type u} (_site : USize) (x : α) : α := x

/-- Records a hit on `site` and returns `true`. -/
@[extern "leancov_mark", noinline, never_extract]
public def mark (_site : USize) : Bool := true

/-- Wraps a `Decidable` instance so true/false branch outcomes are recorded while preserving
dependent proofs `h : p` and `h : ¬p`. -/
@[inline] public def decide (tSite fSite : USize) {p : Prop} [d : Decidable p] : Decidable p :=
  match d with
  | isTrue h => hit tSite fun () => isTrue h
  | isFalse h => hit fSite fun () => isFalse h

end LeanCov
