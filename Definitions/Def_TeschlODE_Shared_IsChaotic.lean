import Mathlib
import Definitions.Def_TeschlODE_Shared_IsTopTransitive

namespace TeschlODE.Shared

/-- Teschl, §11.3, p. 296 (Devaney's definition as used in the book): a discrete dynamical
system `(M, f)` on a metric space `M`, with `f` continuous and `M` infinite, is chaotic if `f`
is topologically transitive and the periodic points `Per(f) = {x | fⁿ(x) = x for some n ≥ 1}`
are dense in `M`. There is no sensitivity clause (that is Lemma 11.3). -/
def IsChaotic {M : Type*} [MetricSpace M] (f : M → M) : Prop :=
  Continuous f ∧ Infinite M ∧ IsTopTransitive f ∧ Dense (Function.periodicPts f)

end TeschlODE.Shared
