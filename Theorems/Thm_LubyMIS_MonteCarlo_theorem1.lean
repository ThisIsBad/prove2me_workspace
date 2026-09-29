import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- THEOREM 1 (Luby 1986, §3.4, p. 1040). For the current graph `H = G′` and `n ≥ max(1, |V′|)` the
number of vertices of the input graph, one execution of the loop body eliminates in expectation
(1) at least `⅛ · |E′| − 1/16` edges under Algorithm A, and
(2) at least `⅛ · |E′|` edges under Algorithm B. -/
theorem theorem1 {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] :
    expA n (fun π => (eliminated H (selectA H π) : ℝ)) ≥
        1 / 8 * (H.edgeFinset.card : ℝ) - 1 / 16 ∧
      expB H (fun c => (eliminated H (selectB H c) : ℝ)) ≥ 1 / 8 * (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.MonteCarlo
