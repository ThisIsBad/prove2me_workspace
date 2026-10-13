import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring

namespace OnlineStochMatching.TSM

/-- **The note of §4.2.1** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching:
Beating 1-1/e*, arXiv:0905.4100v1, p. 7): for a maximum flow edge set `E_f` and a TSM colouring
`(blue, red)` of it, every impression type `i` is incident to either no coloured edge, exactly one
blue edge (and no red edge), or exactly one blue and exactly one red edge. In particular "the ad
along `i`'s blue edge" and "the ad along `i`'s red edge" are well defined. -/
theorem impression_incidence {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red)
    (i : I) :
    (degI blue i = 0 ∧ degI red i = 0) ∨ (degI blue i = 1 ∧ degI red i = 0) ∨
      (degI blue i = 1 ∧ degI red i = 1) := by sorry

end OnlineStochMatching.TSM

