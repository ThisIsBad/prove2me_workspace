import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §3, (3), p. 590 (unnumbered statement): in the two-state specialization of
the general model, `TP = P + π − πP` and
`V_β(P) = min{CP + βV_β(TP); I + βPV_β(1) + β(1 − P)V_β(π); R + βV_β(π)}`, `P ∈ [0, 1]`.

Here `V_β(P)` is `V2 β π C I R P`, the general `V_β` of the two-state instance `twoState` at
the belief `(1 − P, P)`.

**Formalization Note.** Standing hypotheses of §3: `0 < β < 1`, `0 ≤ π ≤ 1` (so that `1 − π`,
`π` are transition probabilities) and `C < I < R` ("It shall be assumed throughout that
`C < I < R`"); `0 < C` is implicit in the paper (the bad state costs `C`, the good state `0`).
-/
theorem equation_3 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) 1,
      V2 β π C I R P =
        min (rhs3 β π C I R (V2 β π C I R) P .produce)
          (min (rhs3 β π C I R (V2 β π C I R) P .inspect)
            (rhs3 β π C I R (V2 β π C I R) P .revise)) := by sorry

end RossQC.Regions

