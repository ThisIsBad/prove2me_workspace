import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Theorem 2 of Mizuno–Todd–Ye (p. 10): let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`. Algorithm 2 with
`N = N_∞(β)` or `N_∞⁻(β)`, started at `(x⁰, s⁰) ∈ N` with `(x⁰)ᵀs⁰ ≤ 2^t`, reaches
`(x^k)ᵀs^k ≤ 2^{−t}` within `K = ⌈ln 2 · n · t / (2βγ(1 − γ))⌉` iterations — the explicit count
behind the paper's `O(nt)`, from (15). A run is any sequence of pairs that starts as required
and makes an Algorithm 2 step from every iterate with `(x^k)ᵀs^k > 2^{−t}`. -/
theorem theorem_2 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (t : ℝ) (x s : ℕ → Fin n → ℝ)
    (h0 : (x 0, s 0) ∈ N) (h0t : x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t)
    (hrun : ∀ k, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k → Alg2Step A N γ (x k) (s k) (x (k + 1)) (s (k + 1))) :
    ∃ k ≤ ⌈Real.log 2 * n * t / (2 * β * γ * (1 - γ))⌉₊, x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.WideNbhd

