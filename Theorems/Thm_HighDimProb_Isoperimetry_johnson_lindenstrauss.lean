import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Theorem 5.3.1** (Johnson-Lindenstrauss Lemma), Vershynin, *High-Dimensional Probability*
(2018), p. 118.

Let `X` be a set of `N` points in `ℝⁿ` and `ε > 0`. Assume that `m ≥ (C/ε²) log N`. Consider a
random `m`-dimensional subspace `E` in `ℝⁿ` uniformly distributed in `G_{n,m}`. Denote the
orthogonal projection onto `E` by `P`. Then, with probability at least `1 − 2exp(−cε²m)`, the
scaled projection `Q := √(n/m) P` is an approximate isometry on `X`:

`(1 − ε) ‖x − y‖₂ ≤ ‖Qx − Qy‖₂ ≤ (1 + ε) ‖x − y‖₂` for all `x, y ∈ X`. -/
theorem johnson_lindenstrauss :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (X : Finset (EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε),
        (m : ℝ) ≥ (C / ε ^ 2) * Real.log (X.card : ℝ) →
        ∀ (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
        IsUniformProjection Prob m P →
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | ∀ x ∈ X, ∀ y ∈ X,
            (1 - ε) * ‖x - y‖ ≤ ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ∧
            ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ≤ (1 + ε) * ‖x - y‖} := by sorry

end HighDimProb.Isoperimetry

