import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- p. 411: on two machines, adding `G` to all processing times (all nonnegative) raises, at every node `J_r`
with `1 ≤ r ≤ n - 1`, both `T̂_r` and `Ŝ_r` by `G [r(n-r) + ½(n-r)(n-r+1) + (n-r)]`,
`Σ_{J_r} d_i` by `½ G r (r + 3)` (the page prints `½ r (r + 3)`, without `G`), and
`LB(J_r)` by `½ G n (n + 3)`. -/
theorem lowerBound2_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J.Nodup) (hr1 : 1 ≤ J.length) (hrn : J.length + 1 ≤ n) :
    That (fun i => a i + G) (fun i => b i + G) J =
      That a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    Shat (fun i => a i + G) (fun i => b i + G) J =
      Shat a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    (state2 (fun i => a i + G) (fun i => b i + G) J).2.2 =
      (state2 a b J).2.2 + G * (J.length : ℝ) * ((J.length : ℝ) + 3) / 2 ∧
    lowerBound2 (fun i => a i + G) (fun i => b i + G) J =
      lowerBound2 a b J + G * n * (n + 3) / 2 := by sorry

end IgnallSchrage.Invariance

