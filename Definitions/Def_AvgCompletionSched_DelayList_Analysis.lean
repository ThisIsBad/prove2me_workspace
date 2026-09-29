import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

open MeasureTheory

variable {n : ℕ}

/-- `p(A) = ∑_{k ∈ A} p_k`, the total processing time of a set of jobs (p. 158). -/
noncomputable def psum (I : Instance n) (A : Finset (Fin n)) : ℝ := ∑ k ∈ A, I.p k

open Classical in
/-- `B_i` (Definition 4.3, p. 159): the jobs which come before `J_i` in the list `π`, including
`J_i` itself. -/
noncomputable def listB (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => π.symm k ≤ π.symm i

open Classical in
/-- `A_i` (Definition 4.3, p. 159): the jobs which come after `J_i` in the list `π`. -/
noncomputable def listA (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => π.symm i < π.symm k

namespace DelayListRun

variable {I : Instance n} {m : ℕ} (D : DelayListRun I m)

open Classical in
/-- `O_i` (Definition 4.3, p. 159): the jobs which are scheduled before `J_i` by the algorithm but
come later in the list than `J_i`. -/
noncomputable def outOfOrder (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  (listA π i).filter fun k => D.Before k i

/-- Total idle time charged to the jobs of `A` that lies in the time set `T`. -/
noncomputable def chargedToIn (A : Finset (Fin n)) (T : Set ℝ) : ℝ :=
  ∑ k ∈ A, ∫ t in D.chargedSet k ∩ T, D.idle t

/-- One backward step of the path `P′` of Definition 4.4 (p. 159): `a` is a predecessor of `b`
with `C^m_a ≥ r_b`, and has the largest completion time among all predecessors `c` of `b` with
`C^m_c ≥ r_b` (ties broken arbitrarily). -/
def PathStep (a b : Fin n) : Prop :=
  I.prec a b ∧ I.r b ≤ D.C a ∧ ∀ c, I.prec c b → I.r b ≤ D.C c → D.C c ≤ D.C a

/-- The list `j₁ :: l = [J_{j₁}, J_{j₂}, …, J_{j_ℓ}]` is a path `P′_i` of Definition 4.4
(p. 159) for job `i` with respect to the run `D`: it ends at `J_{j_ℓ} = J_i`, each job is the
predecessor chosen by `PathStep` for the next one, and the process terminates at `J_{j₁}`,
which has no predecessor `c` with `C^m_c ≥ r_{j₁}`. -/
def IsPathPrime (i j₁ : Fin n) (l : List (Fin n)) : Prop :=
  (j₁ :: l).getLast (List.cons_ne_nil _ _) = i ∧
  List.IsChain D.PathStep (j₁ :: l) ∧
  ∀ c, I.prec c j₁ → D.C c < I.r j₁

end DelayListRun

/-- `κ′_i` (Definition 4.4, p. 159) for the path `j₁ :: l`: the sum of the lengths of the time
intervals `(0, r_{j₁}]`, `(s^m_{j₁}, C^m_{j₁}]`, …, `(s^m_{j_ℓ}, C^m_{j_ℓ}]`, i.e.
`r_{j₁} + ∑_k p_{j_k}`. -/
noncomputable def kappaPrime (I : Instance n) (j₁ : Fin n) (l : List (Fin n)) : ℝ :=
  I.r j₁ + ((j₁ :: l).map I.p).sum

end AvgCompletionSched.DelayList
