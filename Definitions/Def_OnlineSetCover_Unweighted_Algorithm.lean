import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy

namespace OnlineSetCover.Unweighted

open OnlinePrimalDual.OnlineSetCover

/-- The state of the unweighted algorithm of Alon et al. (2009, §2, p. 363): the current weight
`w S` of every set `S` and the current cover `𝒞` (a finite family of set indices). -/
structure State (T : Type*) where
  /-- the weight `w_S` of each set -/
  w : T → ℝ
  /-- the family `𝒞` of sets chosen so far -/
  cover : Finset T

/-- The initial state (p. 363): `w_S = 1/(2m)` for every set `S`, where `m = |T|` is the number
of sets, and the empty cover `𝒞 = ∅`. -/
noncomputable def initState (T : Type*) [Fintype T] : State T where
  w := fun _ => 1 / (2 * (Fintype.card T : ℝ))
  cover := ∅

open Classical in
/-- The potential `Φ = ∑_{j ∉ C} n^{2 w_j}` (p. 363), where `n = |E|` is the number of
elements, `C` is the set of elements covered by the family `cover`, and `w_j = ∑_{S ∋ j} w_S`
is the element weight. -/
noncomputable def potential {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (cover : Finset T) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬ coveredBy inst cover j),
    (Fintype.card E : ℝ) ^ (2 * elementWeight inst w j)

/-- Step 2(a) (p. 363): `k` is the minimal integer with `2^k · x > 1`. It is a natural number
whenever `x < 1` (the only case in which the algorithm uses it), since then `2^k · x ≤ x < 1`
for every integer `k ≤ 0`. -/
def IsAugExponent (x : ℝ) (k : ℕ) : Prop :=
  1 < (2 : ℝ) ^ k * x ∧ ∀ k' : ℕ, k' < k → (2 : ℝ) ^ k' * x ≤ 1

/-- Step 2(b) (p. 363): every set `S ∈ 𝒮_j` (a set containing the arriving element `j`) has
its weight multiplied by `2^k`; the other weights are unchanged. -/
def augment {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (j : E) (k : ℕ) : T → ℝ :=
  fun S => if S ∈ inst.elemSets j then (2 : ℝ) ^ k * w S else w S

/-- The bound "`4 log n`" on the number of sets added in step 2(c) (p. 363), with the natural
logarithm, rounded up to an integer: `⌈4 ln n⌉`. -/
noncomputable def setCap (n : ℕ) : ℕ := ⌈4 * Real.log n⌉₊

/-- One iteration of the algorithm (p. 363) when the adversary gives element `j`, taking state
`s` to state `s'`; the flag `aug` records whether a weight augmentation is performed.
1. If `w_j ≥ 1`, nothing changes.
2. Otherwise (`w_j < 1`): with `k` the minimal integer such that `2^k w_j > 1`, multiply the
   weight of every set containing `j` by `2^k`, and add to the cover a family `F` of at most
   `⌈4 ln n⌉` sets containing `j`, chosen so that the potential after the iteration does not
   exceed the potential before it. The choice of `F` is not determined by the paper, so this is
   a relation: every admissible choice is a step. -/
inductive Step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) : State T → E → State T → Bool → Prop
  | noAug (s : State T) (j : E) (h : 1 ≤ elementWeight inst s.w j) :
      Step inst s j s false
  | aug (s : State T) (j : E) (k : ℕ) (F : Finset T)
      (hlt : elementWeight inst s.w j < 1)
      (hk : IsAugExponent (elementWeight inst s.w j) k)
      (hF : F ⊆ inst.elemSets j)
      (hcard : F.card ≤ setCap (Fintype.card E))
      (hΦ : potential inst (augment inst s.w j k) (s.cover ∪ F) ≤ potential inst s.w s.cover) :
      Step inst s j ⟨augment inst s.w j k, s.cover ∪ F⟩ true

/-- `RunFrom inst s σ s' a`: processing the arrival list `σ` (in order) from state `s`, one
`Step` per arrival, the algorithm can end in state `s'` having performed exactly `a` weight
augmentations. -/
inductive RunFrom {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) : State T → List E → State T → ℕ → Prop
  | nil (s : State T) : RunFrom inst s [] s 0
  | cons {s s' s'' : State T} {j : E} {σ : List E} {b : Bool} {a : ℕ} :
      Step inst s j s' b → RunFrom inst s' σ s'' a →
      RunFrom inst s (j :: σ) s'' ((if b then 1 else 0) + a)

/-- `Run inst σ s a`: a run of the algorithm from its initial state on the arrival list `σ`
ends in state `s` after exactly `a` weight augmentations. -/
def Run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (s : State T) (a : ℕ) : Prop :=
  RunFrom inst (initState T) σ s a

end OnlineSetCover.Unweighted
