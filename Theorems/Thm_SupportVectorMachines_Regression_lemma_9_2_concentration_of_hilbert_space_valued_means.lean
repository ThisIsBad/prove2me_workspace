import Mathlib

open MeasureTheory TopologicalSpace

namespace SupportVectorMachines.Regression

/-- Lemma 9.2, p. 336: let `Z` be a measurable space, `P` a distribution on `Z`, `H` a separable
Hilbert space, and `g : Z → H` measurable with `‖g‖_q := (E_P‖g‖^q_H)^{1/q} < ∞` for some
`q ∈ (1,∞)`. Write `q* := min{1/2, 1/q'}` where `1/q + 1/q' = 1`, i.e. `q* = min{1/2, 1 - 1/q}`.
Then there is a universal constant `c_q > 0` such that, for all `ε > 0` and `n ≥ 1`,
`P^n{(z₁,…,zₙ) : ‖(1/n)∑ᵢg(zᵢ) - E_Pg‖_H ≥ ε} ≤ c_q (‖g‖_q / (ε n^{q*}))^q`. -/
theorem lemma_9_2_concentration_of_hilbert_space_valued_means
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]
    (g : Z → H) (hg : Measurable g)
    (q : ℝ) (hq : 1 < q) (hgInt : Integrable (fun z => ‖g z‖ ^ q) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => P))
          {z : Fin n → Z | ε ≤ ‖(n : ℝ)⁻¹ • (∑ i, g (z i)) - ∫ z', g z' ∂P‖} ≤
        ENNReal.ofReal
          (c * ((∫ z, ‖g z‖ ^ q ∂P) ^ (1 / q) /
              (ε * (n : ℝ) ^ (min (1 / 2 : ℝ) (1 - 1 / q)))) ^ q) := by sorry

end SupportVectorMachines.Regression
