import Mathlib

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, § 4, Lemma, p. 321. For row-wise parameters `q`
(elements of arbitrary sets `S i`, e.g. sets of functions of time) and a fixed `t ≥ 0`, let
`T₁(x)_i = Max_q [b₁_i(q, t) + ∫_0^t Σ_j a_ij(q, s) x_j(s) ds]` and
`T₂(y)_i = Max_q [b₂_i(q, t) + ∫_0^t Σ_j a_ij(q, s) y_j(s) ds]`, the maxima attained. Then, with
`‖x‖ = Σ_i |x_i|` and `‖A‖ = Σ_{i,j} |a_ij|` (3.5),
`‖T₁(x) − T₂(y)‖ ≤ Max_q [‖b₁(q, t) − b₂(q, t)‖ + ∫_0^t ‖A(q, s)‖ ‖x(s) − y(s)‖ ds]`;
stated as: the right-hand side is at least the left-hand side for some admissible joint `q`. -/
theorem operator_estimate {N : ℕ} {P : Fin N → Type*}
    (a : (i : Fin N) → P i → ℝ → Fin N → ℝ) (b₁ b₂ : (i : Fin N) → P i → ℝ)
    (S : (i : Fin N) → Set (P i)) (t : ℝ) (ht : 0 ≤ t)
    (x y : ℝ → Fin N → ℝ) (hx : ContinuousOn x (Set.Icc 0 t)) (hy : ContinuousOn y (Set.Icc 0 t))
    (ha : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N,
      MeasureTheory.IntegrableOn (fun s => a i q s j) (Set.Icc 0 t))
    (T₁ T₂ : Fin N → ℝ)
    (hT₁ : ∀ i : Fin N, IsGreatest
      ((fun q => b₁ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * x s j) '' S i) (T₁ i))
    (hT₂ : ∀ i : Fin N, IsGreatest
      ((fun q => b₂ i q + ∫ s in (0 : ℝ)..t, ∑ j, a i q s j * y s j) '' S i) (T₂ i)) :
    ∃ q ∈ Set.pi Set.univ S,
      ∑ i, |T₁ i - T₂ i| ≤
        ∑ i, |b₁ i (q i) - b₂ i (q i)| +
          ∫ s in (0 : ℝ)..t, (∑ i, ∑ j, |a i (q i) s j|) * ∑ j, |x s j - y s j| := by sorry

end BellmanDP.Markovian

