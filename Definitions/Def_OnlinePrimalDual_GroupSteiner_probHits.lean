import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The probability `ℙ[C ∩ S ≠ ∅]` that the random cover `C` drawn from `ρ` contains at least one
edge of a fixed finite edge set `S`. Used to state the probability that a group `g` is covered,
with `S` the image under a vertex-to-incident-edge map of `g`'s vertices (Buchbinder & Naor, FnT
TCS 2009, Lemma 11.3, p. 231: "the probability that there exists `vᵢ ∈ C`"). -/
def RandomCover.probHits {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E)
    (S : Finset E) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C => ∃ e ∈ S, e ∈ C), ρ.p C

end OnlinePrimalDual.GroupSteiner
