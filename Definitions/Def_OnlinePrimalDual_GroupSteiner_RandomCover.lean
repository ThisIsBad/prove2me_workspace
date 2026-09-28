import Mathlib

namespace OnlinePrimalDual.GroupSteiner

/-- A finite probability distribution over subsets of a finite edge type `E`, representing the
random edge-cover `C` produced by the online randomized rounding scheme of Buchbinder & Naor,
*The Design of Competitive Online Algorithms via a Primal-Dual Approach*, FnT TCS 2009, Section
11.2 (p. 229-230, PDF p. 140-141), at a given point in its execution. `p C` is the probability
that the algorithm's random cover equals exactly the edge set `C`. -/
structure RandomCover (E : Type*) [Fintype E] [DecidableEq E] where
  /-- `p C` is the probability that the random cover equals exactly `C`. -/
  p : Finset E → ℝ
  hp_nonneg : ∀ C, 0 ≤ p C
  hp_sum : ∑ C, p C = 1

end OnlinePrimalDual.GroupSteiner
