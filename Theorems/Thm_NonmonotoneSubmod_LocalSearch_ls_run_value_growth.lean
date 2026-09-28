import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, last paragraph: each
iteration of Algorithm LS increases the value by a factor of at least `1 + ε/n²`, so after `k`
steps from the start `{v}`, `f(S_k) ≥ (1 + ε/n²)^k f({v})`. -/
theorem ls_run_value_growth {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (hε : 0 < ε)
    (f : Finset X → ℝ) (S : ℕ → Finset X) (k : ℕ) (hrun : IsLSRun ε f S k) (v : X)
    (hv : S 0 = {v}) :
    (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k * f {v} ≤ f (S k) := by sorry

end NonmonotoneSubmod.LocalSearch
