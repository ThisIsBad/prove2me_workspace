import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_BNCovPack_SetCover_FracScheme
import Definitions.Def_BNCovPack_SetCover_Potential

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- State of the online integral set-cover algorithm of §5.1 (p. 12): the state of the fractional
scheme of Section 3 (whose weights are the `w(s)` of the potential) and the chosen family `C`. -/
structure State (T : Type*) where
  frac : FracState T
  cover : Finset T

/-- Processing one set `s` after a fractional round whose new weights are `w'` (p. 12, the
rounding rule: "Each time the weight of a set `s` is augmented in Line 2(b) of the algorithm, add
`s` to the cover `C` if its addition does not increase the value of the potential function `Φ`").
If the weight of `s` was augmented (`w s < w' s`), it is raised to `w' s`, and `s` is added to
`C` when `s ∉ C` and `Φ(raised weights, C ∪ {s}) ≤ Φ(w, C)`, the value of `Φ` before the
augmentation of `s`. Otherwise nothing changes. -/
noncomputable def augmentSet {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (OPT : ℕ) (w' : T → ℝ)
    (p : (T → ℝ) × Finset T) (s : T) : (T → ℝ) × Finset T :=
  if p.1 s < w' s then
    let w₁ := Function.update p.1 s (w' s)
    if s ∉ p.2 ∧ potential inst α OPT w₁ (insert s p.2) ≤ potential inst α OPT p.1 p.2 then
      (w₁, insert s p.2)
    else (w₁, p.2)
  else p

/-- One round of the integral algorithm on arrival of element `e`: run the fractional scheme of
Section 3 with `ℓ = d` (p. 5 and p. 12), then process the sets one at a time in the order of the
list `ord`, applying `augmentSet` with `α = alphaParam n OPT`, `n = |E|`. -/
noncomputable def step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (st : State T) (e : E) :
    State T :=
  let f' := fracStep inst B d st.frac e
  let p := ord.foldl (augmentSet inst (alphaParam (Fintype.card E) OPT) OPT f'.w)
    (st.frac.w, st.cover)
  { frac := f', cover := p.2 }

/-- The state of the integral algorithm after the arrival list `σ`, starting from all weights `0`
and the empty cover. -/
noncomputable def run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (σ : List E) : State T :=
  σ.foldl (step inst B d OPT ord) ⟨FracState.init T, ∅⟩

end BNCovPack.SetCover
