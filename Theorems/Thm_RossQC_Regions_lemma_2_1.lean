import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1: "`V_β(P)` is a concave function of `P` — i.e. if
`P = λP¹ + (1 − λ)P²`; then `V_β(P) ≧ λV_β(P¹) + (1 − λ)V_β(P²)`."

Under the standing hypotheses of §1–§2 (`Model.Valid`), `V_β` is concave on the belief simplex
`S`. (`ConcaveOn` includes the convexity of `S`.)

**Formalization Note.** `V_β` is the limit of value iteration from `V⁰ = 0` (`Model.Vβ`). -/
theorem lemma_2_1 {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    ConcaveOn ℝ M.simplex M.Vβ := by sorry

end RossQC.Regions

