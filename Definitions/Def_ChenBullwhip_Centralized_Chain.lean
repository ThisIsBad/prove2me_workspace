import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- p. 440, §3: the order-up-to point of stage `k` with centralized demand information,
`yᵏₜ = L_k D̂ₜ + z_k σ̂^{L_k}_{et}`, where `D̂ₜ = ∑_{i=1}^p D_{t-i}/p` and
`σ̂^{L_k}_{et} = C_{L_k,ρ} √(∑_{i=1}^p (e_{t-i})²/p)`. Stage `k` has lead time `L k` and safety
factor `z k`; the unspecified constant `C_{L_k,ρ}` is `C (L k)`. It is the §2 order-up-to point
with lead time `L k`. -/
noncomputable def AR1Demand.chainLevel (X : AR1Demand P) (p : ℕ) (L : ℕ → ℕ) (C z : ℕ → ℝ)
    (k : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.orderUpTo (C (L k)) (z k) (L k) p t ω

/-- pp. 440–441, §3 (sequence of events): the order `qᵏₜ` placed by stage `k` in period `t`.
Stage 1 orders `q¹ₜ = y¹ₜ - y¹_{t-1} + D_{t-1}`; stage `k ≥ 2` receives the order `q^{k-1}_t`
and orders `qᵏₜ = yᵏₜ - yᵏ_{t-1} + q^{k-1}_t`. The value at `k = 0` is the convention
`q⁰ₜ = D_{t-1}` (the customer demand seen at the end of period `t - 1`); stages are numbered from 1. -/
noncomputable def AR1Demand.chainOrder (X : AR1Demand P) (p : ℕ) (L : ℕ → ℕ) (C z : ℕ → ℝ) :
    ℕ → ℤ → Ω → ℝ
  | 0, t, ω => X.D (t - 1) ω
  | k + 1, t, ω =>
      X.chainLevel p L C z (k + 1) t ω - X.chainLevel p L C z (k + 1) (t - 1) ω
        + X.chainOrder p L C z k t ω

end ChenBullwhip.Centralized
