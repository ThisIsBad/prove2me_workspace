import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
Configurations, runs and selectable sets (Johnson 1974, p. 266).
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- A configuration `K = ⟨N_K, UNCOV_K, ⟨SET_K[1], …, SET_K[N_K]⟩⟩` of algorithm C1, with
`⋃_{i=1}^{N_K} SET_K[i] = UNCOV_K`. The index type `ι` plays the role of `{1, …, N_K}`. -/
structure Config (ι α : Type) [Fintype ι] [DecidableEq α] where
  UNCOV : Finset α
  SET : ι → Finset α
  union_eq : Finset.univ.biUnion SET = UNCOV

/-- The configuration of C1 after it has been given input `F` and initialized itself via
Step 1: `UNCOV = ⋃ S_i`, `SET[i] = S_i`. -/
def initConfig (S : ι → Finset α) : Config ι α := ⟨ground S, S, rfl⟩

/-- If the algorithm enters Step 2 in configuration `K`, it does not halt
(`UNCOV_K ≠ ∅`), it can choose `j` at Step 3 (`|SET_K[j]|` is maximal), and the resulting
configuration after updating at Step 4 is `K'`. -/
def ConfigStep (K : Config ι α) (j : ι) (K' : Config ι α) : Prop :=
  K.UNCOV ≠ ∅ ∧ (∀ i, (K.SET i).card ≤ (K.SET j).card) ∧
    K'.UNCOV = K.UNCOV \ K.SET j ∧ K'.SET = fun i => K.SET i \ K.SET j

/-- `IsRun K js`: there is a run `R = ⟨K(1), j(1), K(2), …, j(t−1), K(t)⟩` from `K` whose
sequence of chosen integers is `js = [j(1), …, j(t−1)]`: `K(1) = K`, each `K(i+1)` results from
`K(i)` by `ConfigStep` with choice `j(i)` (so `UNCOV_{K(i)} ≠ ∅` for `i < t`), and
`UNCOV_{K(t)} = ∅`. -/
inductive IsRun : Config ι α → List ι → Prop
  | halt (K : Config ι α) : K.UNCOV = ∅ → IsRun K []
  | step (K : Config ι α) (j : ι) (K' : Config ι α) (js : List ι) :
      ConfigStep K j K' → IsRun K' js → IsRun K (j :: js)

variable [DecidableEq ι]

/-- `M` is selectable from `K`: there is a run `R` from `K` with `M = Numbers(R)`, the set of the
`j`'s in `R`. -/
def Selectable (K : Config ι α) (M : Finset ι) : Prop :=
  ∃ js : List ι, IsRun K js ∧ M = js.toFinset

end JohnsonApprox.SetCover
