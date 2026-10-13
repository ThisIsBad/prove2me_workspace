import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.2: "Every β-optimal policy produces at all `P` such that
`0 ≦ P ≦ π`."

In the two-state model, for every `P ∈ [0, π]` producing is the unique minimizer of the right side
of (3): it is strictly cheaper than inspecting and strictly cheaper than revising.

**Formalization Note.** "Every β-optimal policy produces at `P`" is formalized as "produce is the
unique action attaining the minimum in (3) at `P`", since a β-optimal rule is one selecting a
minimizer (p. 588). `V_β(P)` is `V2 β π C I R P`. Standing hypotheses of §3: `0 < β < 1`,
`0 ≤ π ≤ 1`, `C < I < R`, and the implicit `0 < C`. -/
theorem lemma_3_2 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) π,
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .inspect ∧
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .revise := by sorry

end RossQC.Regions

