import Mathlib

namespace LogRegretOCO.FTAL

/-- Follow the Leader (Hazan–Agarwal–Kale 2007, §3.3, p. 179): `x` is a run of FTL on the cost
functions `f` over the decision set `P` if, for every round `t ≥ 1`, the point `x t` lies in `P`
and minimises the cumulative cost of the rounds `1, …, t - 1` over `P`. Rounds are 1-based and
`x 0` is unused. At `t = 1` the sum is empty, so `x 1` is an arbitrary point of `P`. Any
tie-breaking rule among minimisers gives a run. -/
def IsFTLRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    x t ∈ P ∧ ∀ y ∈ P, ∑ τ ∈ Finset.Ico 1 t, f τ (x t) ≤ ∑ τ ∈ Finset.Ico 1 t, f τ y

end LogRegretOCO.FTAL
