import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_LoewnerLE

open MeasureTheory

namespace HighDimStat.RandomMatrices

/-- **Definition 6.10** (Bernstein's condition for matrices), Wainwright, *High-Dimensional
Statistics* (2019), p. 171, Eq. (6.29). A zero-mean symmetric random matrix `Q` satisfies a
Bernstein condition with parameter `b > 0` if `E[Q^j] ⪯ (1/2) j! b^{j-2} var(Q)` for
`j = 3, 4, ...`. Integrability of every entry of every relevant matrix power is required
explicitly, guarding against the Bochner integral's junk value on a non-integrable function. -/
def BernsteinConditionMatrix {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ) (Prob : Measure Ω) (b : ℝ) : Prop :=
  (∀ᵐ ω ∂Prob, (Q ω).IsSymm) ∧
  (∀ j : ℕ, ∀ i k : Fin d, Integrable (fun ω => (Q ω ^ j) i k) Prob) ∧
  matrixExpectation Q Prob = 0 ∧
  (∀ j : ℕ, 3 ≤ j →
    LoewnerLE (matrixExpectation (fun ω => Q ω ^ j) Prob)
      ((1 / 2 * (Nat.factorial j : ℝ) * b ^ (j - 2)) • matrixVariance Q Prob))

end HighDimStat.RandomMatrices
