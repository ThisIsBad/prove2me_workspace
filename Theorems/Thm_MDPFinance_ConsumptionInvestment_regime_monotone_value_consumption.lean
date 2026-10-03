import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary
import Definitions.Def_MDPFinance_ConsumptionInvestment_StochasticOrders

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.4.5 (Bäuerle–Rieder, p. 105, PDF 119). One stock (`d = 1`), `E_Y = Fin m` linearly
ordered, the support of `R(j)` independent of `j` (a common admissible set `Ã`, `hsupp`), `(Y_n)`
stochastically monotone, `Q_j ≤_icv Q_k` whenever `j ≤ k`. With the power-utility solution of
Theorem 4.4.2 (positive `d_n(j)`, `c_n^*(x,j) = x(γd_n(j))^{-δ}`,
`a_n^*(x,j) = (x-c_n^*(x,j))α^*(j)`): a) `J_n(x,j) = d_n(j)x^γ` is increasing in `j` and
`c_n^*(x,j)` is decreasing in `j`; b) if `α^*(j) ≥ 0` for every `j` then `a_n^*(x,j)` is
increasing in `j`. -/
theorem regime_monotone_value_consumption {m : ℕ} (M : RegimeSwitchingMarket (Fin m) 1)
    (hsupp : ∀ j k : Fin m, M.Afrac j = M.Afrac k)
    (hmono : IsStochasticallyMonotoneChain M.p)
    (hicv : ∀ j k : Fin m, j ≤ k →
      LEIncreasingConcaveOrder ((M.Q j).map (fun z => z 0)) ((M.Q k).map (fun z => z 0)))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ) (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → Fin m → ℝ) (hdpos : ∀ n j, 0 < dseq n j) (hd0 : ∀ j, dseq 0 j = γ⁻¹)
    (hdrec : ∀ n, ∀ j,
      dseq (n + 1) j ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        (M.β * (1 + M.i) ^ γ * M.vPower γ j) ^ ((1 - γ)⁻¹) *
          ∑ k, M.p j k * dseq n k ^ ((1 - γ)⁻¹))
    (αstar : Fin m → (Fin 1 → ℝ)) (hαstar_mem : ∀ j, αstar j ∈ M.Afrac j)
    (hαstar_opt : ∀ j, ∫ z, (1 + ∑ k, αstar j k * z k) ^ γ ∂(M.Q j) = M.vPower γ j) :
    (∀ n, Monotone (dseq n)) ∧
      (∀ n, ∀ x ≥ (0 : ℝ), Antitone (fun j => x * (γ * dseq n j) ^ (-(1 - γ)⁻¹))) ∧
      ((∀ j, 0 ≤ αstar j 0) → ∀ n, ∀ x ≥ (0 : ℝ), Monotone (fun j =>
        (x - x * (γ * dseq n j) ^ (-(1 - γ)⁻¹)) * αstar j 0)) := by sorry

end MDPFinance.ConsumptionInvestment
