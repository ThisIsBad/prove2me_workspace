import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- p. 3, failure accumulation: for `N ≥ 1` and `k ≤ N`, every history of `k` failing steps
(the 0-based step `s` using `|ψ_{2^s α_N}⟩`) has applied `c · U(−α_N)^{2^k − 1}` with
`|c|² = (1/16)^k`; `U(−α_N)^{2^N − 1} = −U(α_N)`; and 8 of the 16 outcomes of a step succeed. -/
theorem failure_accumulation (N : ℕ) (hN : 1 ≤ N) :
    (∀ k ≤ N, ∀ l ∈ failing k, ∃ c : ℂ, Complex.normSq c = (1 / 16 : ℝ) ^ k ∧
        branchKraus N l = c • gate (-alphaN N) ^ (2 ^ k - 1)) ∧
    gate (-alphaN N) ^ (2 ^ N - 1) = -gate (alphaN N) ∧
    (Finset.univ.filter succeeds).card = 8 := by sorry

end EntanglingOps.BinaryPhase

