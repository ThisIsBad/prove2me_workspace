import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.1: "`V_β(P)` is monotone nondecreasing in `P`."

In the two-state model, `P ↦ V_β(P)` is monotone nondecreasing on `[0, 1]`.

**Formalization Note.** `V_β(P)` is `V2 β π C I R P`, the general `V_β` (limit of value iteration
from `V⁰ = 0`) of the two-state instance at the belief `(1 − P, P)`. Standing hypotheses of §3:
`0 < β < 1`, `0 ≤ π ≤ 1`, `C < I < R`, and the implicit `0 < C`. -/
theorem lemma_3_1 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    MonotoneOn (V2 β π C I R) (Set.Icc 0 1) := by sorry

end RossQC.Regions

