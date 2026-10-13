import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring

namespace OnlineStochMatching.TSM

/-- **Equation (1)** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.2, p. 7): for a maximum flow edge set `E_f` and a TSM colouring
`(blue, red)` of it,
`|E_f| = 2|A_BR| + 2|A_BB| + |A_B| + |A_R|`,
where `A_BR`, `A_BB`, `A_B`, `A_R` are the advertisers incident to one blue and one red edge, to
two blue edges, to only a blue edge, and to only a red edge. -/
theorem eq_1 {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red) :
    F.card = 2 * (adsBR blue red).card + 2 * (adsBB blue red).card + (adsB blue red).card +
      (adsR blue red).card := by sorry

end OnlineStochMatching.TSM

