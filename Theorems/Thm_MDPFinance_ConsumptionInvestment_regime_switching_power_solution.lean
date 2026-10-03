import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.4.2 (Bäuerle–Rieder, p. 103, PDF 117). Let `Uc(x)=Up(x)=x^γ/γ`, `0<γ<1`,
`δ:=(1-γ)⁻¹`. Let the positive `(d_n(j))_{n,j}` satisfy `d_0(j) = γ⁻¹` and `d_{n+1}(j)^δ = γ^{-δ}
+ (β(1+i)^γ v(j))^δ Σ_k p_{jk} d_n(k)^δ` (`v(j)` the value of problem (4.20)). Then: a)
`J_n(x,j) = d_n(j) x^γ`, `x ≥ 0`; b) the optimal consumption is `c_n^*(x,j) = x(γd_n(j))^{-δ}`
and the optimal amounts invested in the stocks are `a_n^*(x,j) = (x-c_n^*(x,j))α^*(j)`, `α^*(j)`
the optimal solution of (4.20): for every horizon `N`, the strategy `(f_N^*, …, f_1^*)`,
`f_n^* = (c_n^*, a_n^*)`, is optimal for the `N`-stage problem. -/
theorem regime_switching_power_solution {EY : Type*} [Fintype EY] [MeasurableSpace EY] {d : ℕ}
    (M : RegimeSwitchingMarket EY d) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ) (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → EY → ℝ) (hdpos : ∀ n j, 0 < dseq n j) (hd0 : ∀ j, dseq 0 j = γ⁻¹)
    (hdrec : ∀ n, ∀ j,
      dseq (n + 1) j ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        (M.β * (1 + M.i) ^ γ * M.vPower γ j) ^ ((1 - γ)⁻¹) *
          ∑ k, M.p j k * dseq n k ^ ((1 - γ)⁻¹)) :
    (∀ n, ∀ x ≥ (0 : ℝ), ∀ j, M.J n x j = ((dseq n j * x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : EY → (Fin d → ℝ), (∀ j, αstar j ∈ M.Afrac j ∧
          ∫ z, (1 + ∑ k, αstar j k * z k) ^ γ ∂(M.Q j) = M.vPower γ j) ∧
        ∃ fstar : ℕ → ℝ × EY → ℝ × (Fin d → ℝ),
          (∀ n, ∀ x ≥ (0 : ℝ), ∀ j, (fstar n (x, j)).1 = x * (γ * dseq n j) ^ (-(1 - γ)⁻¹)) ∧
          (∀ n, ∀ x ≥ (0 : ℝ), ∀ j,
            (fstar n (x, j)).2 = fun k => (x - (fstar n (x, j)).1) * αstar j k) ∧
          ∀ N : ℕ, M.IsAdmissible N (fun l => fstar (N - l)) ∧
            ∀ x ≥ (0 : ℝ), ∀ j, M.Jpi (fun l => fstar (N - l)) N x j = M.J N x j) := by sorry

end MDPFinance.ConsumptionInvestment
