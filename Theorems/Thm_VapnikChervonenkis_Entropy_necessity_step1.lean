import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Step 1° of the proof of necessity in Theorem 4 (pp. 276–277), unweakened: with
`Q = {π^(l) > ε}` on samples of size `l` and `C′ = {sup_{A∈S} |ν′_A − ν″_A| > 2ε} = {ρ^(l) > 2ε}` on
double samples of size `2l`, independence of the two semi-samples gives
`1 − P(C′) ≥ (1 − P(Q))²`, i.e. `P(C′) ≤ 2P(Q) − P²(Q)`. `hπ` is the paper's assumption
(p. 265) that `π^(l)` is measurable. -/
theorem necessity_step1 {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    (1 - (Measure.pi (fun _ : Fin l => P)).real {x | ε < Shared.maxDeviation S P l x}) ^ 2
      ≤ 1 - (Measure.pi (fun _ : Fin (l + l) => P)).real
          {x | 2 * ε < Shared.semiSampleDeviation S l x} := by sorry

end VapnikChervonenkis.Entropy
