import Mathlib

namespace FibHeap.Amort
theorem fib_add_two_ge_goldenRatio_pow (k : ℕ) :
    Real.goldenRatio ^ k ≤ (Nat.fib (k + 2) : ℝ) := by sorry
end FibHeap.Amort

