import Mathlib

namespace FoundationsML.Boosting

/-- The convex hull `conv(H)` of a set `H` of real-valued functions `X → ℝ` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Eq. (7.12), p. 157, PDF p. 174): `conv(H) = {∑_{k=1}^p μ_k h_k : p ≥ 1, μ_k ≥ 0, h_k ∈ H,
∑_{k=1}^p μ_k ≤ 1}`. -/
noncomputable def ConvHull {X : Type*} (H : Set (X → ℝ)) : Set (X → ℝ) :=
  {f | ∃ (p : ℕ) (μ : Fin p → ℝ) (hs : Fin p → (X → ℝ)),
    1 ≤ p ∧ (∀ k, 0 ≤ μ k) ∧ (∀ k, hs k ∈ H) ∧ (∑ k, μ k) ≤ 1 ∧
    f = fun x => ∑ k, μ k * hs k x}

end FoundationsML.Boosting
