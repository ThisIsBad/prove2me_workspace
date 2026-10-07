import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Inequalities (2) and (3) of the proof of Theorem 4(d), p. 20: for every processing order `π`,
`Σ_{j>t} p_π(j)(C_π(j) − C_π(t)) = Σ_{t<j≤k≤n} (τ + a_π(j))(τ + a_π(k))
  = ½t'(t'+1)τ² + (t'+1)τ(A − b − c_π) + Σ_{t<j≤k≤n} a_π(j) a_π(k)`, and
`0 ≤ Σ_{t<j≤k≤n} a_π(j) a_π(k) ≤ ½t(t+1)a_*²`. -/
theorem ineq_2_3 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtP a b τ) π t =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (t + tPrime a b) => t ≤ i.val),
          ∑ k ∈ Finset.univ.filter (fun k : Fin (t + tPrime a b) => i ≤ k),
            (wtP a b τ (π i) : ℤ) * wtP a b τ (π k) ∧
    (tailWeighted (wtP a b τ) (wtP a b τ) π t : ℝ) =
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * (τ : ℝ) ^ 2
          + (tPrime a b + 1) * (τ : ℝ) * ((bigA a : ℝ) - b - cPi a b τ π)
          + aPairSum a b π ∧
    0 ≤ aPairSum a b π ∧
    (aPairSum a b π : ℝ) ≤ (1 / 2 : ℝ) * t * (t + 1) * (aStar a : ℝ) ^ 2 := by sorry

end SchedComplexity.Tardiness

