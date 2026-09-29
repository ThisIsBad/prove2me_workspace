import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game
import Definitions.Def_VectorPayoffs_Convex_Recursion

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, proof of THEOREM 1, p. 4, (5)–(7): under THEOREM 1's hypotheses, the
squared distances `δₙ = d(x̄ₙ, S)²` satisfy (5), (6), (7) with `c = (diam X)²` and constants
`a, b` chosen before II's strategy. -/
theorem theorem1_recursion {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (hS : IsClosed S)
    (p : E N → Fin r → ℝ)
    (hsep : ∀ x ∉ S, p x ∈ stdSimplex ℝ (Fin r) ∧ G.BlackwellCondition S (p x) x)
    (f : Strategy N r)
    (hf : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∉ S → f.toFun n h = p (avgHist h)) :
    ∃ a b : ℝ, ∀ (g : Strategy N s) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (x : ℕ → Ω → E N), G.IsPlay f g μ x →
        SatisfiesRecursion a b (Metric.diam G.X ^ 2) μ
          (fun n ω => Metric.infDist (avg x n ω) S ^ 2) := by sorry

end VectorPayoffs.Convex
