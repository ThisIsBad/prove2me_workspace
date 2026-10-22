import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_BNCovPack_SetCover_Potential
import Definitions.Def_BNCovPack_SetCover_Algorithm

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.2** (Buchbinder–Naor 2009, p. 14): the online unweighted set-cover algorithm of §5.1
(unit costs, fractional scheme with `ℓ = d`, rounding by the potential `Φ` with
`α = max {1, ln(r n/OPT)}`), run with any `B > 0`, any processing order of the sets, and a known
value `OPT ≥ 1` such that some family of at most `OPT` sets covers every arriving element,
(i) covers every element that is given to it, and
(ii) chooses at most `(2 α ln(1 + d) + 1) · OPT / ln 2` sets.
The paper writes `OPT · O(log d log(n/OPT))`; the proof yields `(2α ln(1+d) + 1)·OPT/ln 2`. -/
theorem lemma_5_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hc : ∀ s, inst.c s = 1)
    (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (hfreq : ∀ e, (inst.elemSets e).card ≤ d)
    (OPT : ℕ) (hOPT : 1 ≤ OPT) (ord : List T) (hord : ∀ s, s ∈ ord) (σ : List E)
    (hopt : ∃ F : Finset T, F.card ≤ OPT ∧ ∀ e ∈ σ, coveredBy inst F e) :
    (∀ e ∈ σ, coveredBy inst (run inst B d OPT ord σ).cover e) ∧
    ((run inst B d OPT ord σ).cover.card : ℝ)
      ≤ (2 * alphaParam (Fintype.card E) OPT * Real.log (1 + (d : ℝ)) + 1) * (OPT : ℝ)
          / Real.log 2 := by sorry

end BNCovPack.SetCover

