import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- Luby 1986, §3.2, p. 1040: under Algorithm A's law (priorities mutually independent and uniform on
`{1, …, n⁴}`), the priorities are pairwise distinct with probability at least `1 − 1/(2n²)`, where
`n ≥ max(1, |V′|)` is the number of vertices of the input graph. -/
theorem pi_injective_prob {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) :
    probA (V := V) n (fun π => Function.Injective π) ≥ 1 - 1 / (2 * (n : ℝ) ^ 2) := by sorry

end LubyMIS.MonteCarlo
