import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_MultiperiodMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.IndifferencePricing

/-- Theorem 4.9.4 (Bäuerle–Rieder, p. 139, PDF 153) — the goal of this mission. For the
multiperiod financial market it holds: a) `V_n^H(x,s,ŝ) = -e^{-γx}d_n(s,ŝ)` where `(d_n)`
satisfies `d_N(s,ŝ) := e^{γh(s,ŝ)}`, `d_n(s,ŝ) := inf_a 𝔼[e^{-γa(R̃_{n+1}-1)}d_{n+1}(sR̃_{n+1},
ŝR̂_{n+1})]`; in particular `V_n^0(x,s,ŝ) = -e^{-γx}v^{N-n}`. b) The indifference price of `H` is
`v_n(H,s,ŝ) = (1/γ)log(d_n(s,ŝ)/v^{N-n})`. c) The indifference prices satisfy the consistency
condition `v_n(v_{n+1}(H,sR̃_{n+1},ŝR̂_{n+1}),s,ŝ) = v_n(H,s,ŝ)`. All state claims are on the
state space `E = ℝ × ℝ_{>0} × ℝ_{>0}`; the claim `H = h(S_N,Ŝ_N)` is nonnegative (p. 134-135).
Part c) is stated as: whenever `v_{n+1}(H,·,·)` is a time-`(n+1)` indifference-price function of
`H` on `ℝ_{>0}²`, the one-period claim `v_{n+1}(H,S_{n+1},Ŝ_{n+1})` maturing at `n+1` has a
time-`n` indifference price which is also a time-`n` indifference price of `H` (indifference
prices are unique because `V_n^0` is strictly increasing in `x`, so this is the book's equation
`w_n = v_n`). -/
theorem multiperiod_indifference_solution {Ω : Type*} [MeasurableSpace Ω]
    (M : MultiperiodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ) (hh : ∀ s ŝ, 0 ≤ h s ŝ) :
    ∃ dseq : ℕ → ℝ → ℝ → ℝ,
      (∀ s ŝ, dseq M.N s ŝ = Real.exp (M.γ * h s ŝ)) ∧
      (∀ n < M.N, ∀ s ŝ,
        dseq n s ŝ = ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rtilde (n + 1) ω - 1)) *
          dseq (n + 1) (s * M.Rtilde (n + 1) ω) (ŝ * M.Rhat (n + 1) ω) ∂M.measIP) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH h n x s ŝ = -Real.exp (-M.γ * x) * dseq n s ŝ) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH (fun _ _ => 0) n x s ŝ = -Real.exp (-M.γ * x) * M.vGeneric ^ (M.N - n)) ∧
      (∀ n ≤ M.N, ∀ s ŝ, 0 < s → 0 < ŝ →
        M.IsIndifferencePriceAt h M.N n s ŝ
          (1 / M.γ * Real.log (dseq n s ŝ / M.vGeneric ^ (M.N - n)))) ∧
      (∀ n < M.N, ∀ s ŝ, 0 < s → 0 < ŝ → ∀ vnext : ℝ → ℝ → ℝ,
        (∀ s' ŝ', 0 < s' → 0 < ŝ' → M.IsIndifferencePriceAt h M.N (n + 1) s' ŝ' (vnext s' ŝ')) →
        ∃ w : ℝ, M.IsIndifferencePriceAt vnext (n + 1) n s ŝ w ∧
          M.IsIndifferencePriceAt h M.N n s ŝ w) := by sorry

end MDPFinance.IndifferencePricing
