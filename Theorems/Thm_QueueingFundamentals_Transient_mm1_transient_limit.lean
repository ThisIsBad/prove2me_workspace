import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_mm1Transient

namespace QueueingFundamentals.Transient

open Filter Topology

/-- The limit of (2.75) (p.101). For `λ, μ > 0`, every initial size `i` and every `n`:
if `ρ = λ/μ < 1` then `p_n(t) → (1 - ρ) ρ^n` as `t → ∞`; if `λ/μ ≥ 1` then `p_n(t) → 0`. -/
theorem mm1_transient_limit (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) :
    (lam / mu < 1 →
        Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop
          (𝓝 ((1 - lam / mu) * (lam / mu) ^ n))) ∧
      (1 ≤ lam / mu → Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop (𝓝 0)) := by sorry

end QueueingFundamentals.Transient

