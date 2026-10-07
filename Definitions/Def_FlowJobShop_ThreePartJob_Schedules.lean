import Mathlib
import Definitions.Def_FlowJobShop_ThreePartJob_Instance

namespace FlowJobShop.ThreePartJob

/-- A finite preemptive schedule of every operation of a job-shop instance.
Piece `u` processes `op u` during `[start u, finish u)`. Positive-length
pieces on a machine are disjoint; their lengths sum to the operation's
processing time; all pieces of an earlier operation finish before any piece
of a later operation of the same job starts. -/
structure PreemptiveSchedule {m n : ℕ} (inst : JobShopLTAS.Core.Instance m n) where
  pieceCount : ℕ
  op : Fin pieceCount → inst.Op
  start : Fin pieceCount → ℝ
  finish : Fin pieceCount → ℝ
  piece_positive : ∀ u, 0 ≤ start u ∧ start u < finish u
  machine_disjoint : ∀ u v, u ≠ v → inst.mach (op u) = inst.mach (op v) →
    finish u ≤ start v ∨ finish v ≤ start u
  work : ∀ o : inst.Op,
    ∑ u ∈ Finset.univ.filter (fun u => op u = o), (finish u - start u) = inst.proc o
  precedence : ∀ u v, (op u).1 = (op v).1 → (op u).2.val < (op v).2.val →
    finish u ≤ start v

/-- The schedule finishes by `τ` when every piece ends by `τ`. There are no
pieces for zero-length operations, whose completion inherits the end of the
previous operation; this is immaterial to the bound because the previous
piece is included. -/
def PreemptiveSchedule.FinishesBy {m n : ℕ} {inst : JobShopLTAS.Core.Instance m n}
    (S : PreemptiveSchedule inst) (τ : ℝ) : Prop := ∀ u, S.finish u ≤ τ

/-- The published nonpreemptive schedule is feasible and all operations
complete by `τ`. -/
def NonpreemptiveFinishesBy {m n : ℕ} (inst : JobShopLTAS.Core.Instance m n)
    (s : inst.Op → ℝ) (τ : ℝ) : Prop :=
  inst.IsFeasibleSchedule Finset.univ s ∧ ∀ o : inst.Op, s o + inst.proc o ≤ τ

end FlowJobShop.ThreePartJob
