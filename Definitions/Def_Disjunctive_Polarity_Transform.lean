import Mathlib

namespace Disjunctive.Polarity

/-- The projection of a subset of `(Fin q → ℝ) × (Fin w → ℝ) × ℝ` onto its `(v, v0)`-components,
dropping the auxiliary `w`-coordinate (Balas §2.3, p. 32: `Proj_{(v,v0)}(W̃)`). -/
def ProjVW {q w : ℕ} (S : Set ((Fin q → ℝ) × (Fin w → ℝ) × ℝ)) : Set ((Fin q → ℝ) × ℝ) :=
  {p | ∃ ww : Fin w → ℝ, (p.1, ww, p.2) ∈ S}

end Disjunctive.Polarity
