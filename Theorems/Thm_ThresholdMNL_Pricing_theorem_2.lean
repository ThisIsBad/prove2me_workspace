import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 2 (p. 14): if the optimal value `V` of problem (4) on `S_n` is the value over the
feasible prices at which the outside option is not considered, then it is the value of the
outside-excluded profit at the closure point where product 1 has markup
`m*_1 = (α̂_1 − u_0 − Δ)/β`, products `2, …, n'` a common markup `m`, and products `n' + 1, …, n`
nominal utility `u_0`; (a) for `n = 1` the value is `m*_1`; the profit is strictly unimodal in `m`. -/
theorem theorem_2 {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (V : ℝ)
    (hV : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V)
    (hexcl : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        ¬ OutsideInCons (ordAssort N n) α β u0 Δ p ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V) :
    let i₁ : Fin N := ⟨0, by omega⟩
    let m₁ : ℝ := (α i₁ - β * c i₁ - u0 - Δ) / β
    let pbar : ℕ → ℝ → Fin N → ℝ := fun n' m i =>
      if i.val = 0 then c i + m₁ else if i.val < n' then c i + m else (α i - u0) / β
    (n = 1 → V = m₁) ∧
    ∃ (n' : ℕ) (m : ℝ), 1 ≤ n' ∧ n' ≤ n ∧
      V = exclProfit (ordAssort N n) α c β (pbar n' m) ∧
      (∀ i ∈ ordAssort N n,
        u0 ≤ nomUtil α β (pbar n' m) i ∧ nomUtil α β (pbar n' m) i ≤ u0 + Δ) ∧
      (2 ≤ n' → ∃ m₀ : ℝ,
        StrictMonoOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Iic m₀) ∧
        StrictAntiOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Ici m₀)) := by sorry

end ThresholdMNL.Pricing

