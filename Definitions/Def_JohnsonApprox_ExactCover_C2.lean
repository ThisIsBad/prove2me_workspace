import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem

namespace JohnsonApprox.ExactCover

variable {α : Type} [DecidableEq α]

/-- The state of algorithm C2: the paper's `SUB`, `LEFT` (as index sets) and `UNCOV`. -/
structure State (F : Input α) where
  SUB : Finset (Fin F.p)
  LEFT : Finset (Fin F.p)
  UNCOV : Finset α

/-- Step 1 of C2: `SUB = ∅`, `LEFT = F`, `UNCOV = ⋃_{S ∈ F} S`. -/
def init (F : Input α) : State F := ⟨∅, Finset.univ, F.ground⟩

/-- The halting test of Step 2: `UNCOV = ∅`. -/
def Halts {F : Input α} (σ : State F) : Prop := σ.UNCOV = ∅

/-- Step 3 of C2 may choose `S′ = S_i` in state `σ`: `i ∈ LEFT` and `S_i` minimizes
`Ratio(S) = |S − UNCOV| / |S ∩ UNCOV|` over `LEFT`. `Ratio(S)` is `+∞` when `S ∩ UNCOV = ∅`, so
the minimizer meets `UNCOV` and the comparison ranges over the sets of `LEFT` meeting `UNCOV`;
ratios are compared by cross-multiplication. Every minimizer is allowed (ties are free). -/
def MayChoose (F : Input α) (σ : State F) (i : Fin F.p) : Prop :=
  i ∈ σ.LEFT ∧ (F.S i ∩ σ.UNCOV).Nonempty ∧
    ∀ j ∈ σ.LEFT, (F.S j ∩ σ.UNCOV).Nonempty →
      (F.S i \ σ.UNCOV).card * (F.S j ∩ σ.UNCOV).card ≤
        (F.S j \ σ.UNCOV).card * (F.S i ∩ σ.UNCOV).card

/-- One pass through Steps 2–4 of C2 choosing `S′ = S_i`: Step 2 does not halt, Step 3 may choose
`i`, and Step 4 sets `SUB = SUB ∪ {S′}`, `UNCOV = UNCOV − S′`, `LEFT = LEFT − {S′}`. -/
def StepVia (F : Input α) (σ : State F) (i : Fin F.p) (σ' : State F) : Prop :=
  ¬ Halts σ ∧ MayChoose F σ i ∧
    σ' = ⟨insert i σ.SUB, σ.LEFT.erase i, σ.UNCOV \ F.S i⟩

/-- One iteration of C2, for some admissible choice at Step 3. -/
def Step (F : Input α) (σ σ' : State F) : Prop := ∃ i, StepVia F σ i σ'

/-- `σ` is a state C2 can be in, on input `F`, after finitely many iterations. -/
def Reachable (F : Input α) (σ : State F) : Prop := Relation.ReflTransGen (Step F) (init F) σ

/-- `M` is choosable by C2 on input `F`: some admissible run halts with `SUB = M`. -/
def Choosable (F : Input α) (M : Finset (Fin F.p)) : Prop :=
  ∃ σ, Reachable F σ ∧ Halts σ ∧ σ.SUB = M

/-- `RunOV F σ ov`: some run of C2 on `F`, started at Step 1, reaches the state `σ`, and the
cumulative overlap of the sets it added to `SUB` is `ov`. The overlap `ov(S′)` of a chosen set is
`|S′ − UNCOV|` with `UNCOV` taken at the moment `S′` is added to `SUB`. -/
inductive RunOV (F : Input α) : State F → ℕ → Prop
  | init : RunOV F (init F) 0
  | step {σ : State F} {ov : ℕ} {i : Fin F.p} {σ' : State F} :
      RunOV F σ ov → StepVia F σ i σ' → RunOV F σ' (ov + (F.S i \ σ.UNCOV).card)

end JohnsonApprox.ExactCover
