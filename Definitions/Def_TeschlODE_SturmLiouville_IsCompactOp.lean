import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 150: a linear operator `A` defined on all of the inner product space `H₀`
is *compact* if every sequence `A fₙ` has a convergent subsequence whenever `fₙ` is bounded.
The limit is required to lie in `H₀` itself (`H₀` is not assumed complete). -/
def IsCompactOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : Prop :=
  ∀ f : ℕ → E, Bornology.IsBounded (Set.range f) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : E,
      Filter.Tendsto (fun n => A (f (φ n))) Filter.atTop (nhds g)

end TeschlODE.SturmLiouville
