import Mathlib

namespace DelayedSWPT.Model

/-- An instance of the single-machine problem of Anderson and Potts (2004), §1, p. 686, with
the integer data of §2, p. 688: `n` jobs, job `j` has release date `r j`, processing time
`p j ≥ 1` and positive weight `w j`. Jobs are indexed by `Fin n` (0-based). -/
structure Instance (n : ℕ) where
  r : Fin n → ℕ
  p : Fin n → ℕ
  w : Fin n → ℝ
  p_pos : ∀ j, 1 ≤ p j
  w_pos : ∀ j, 0 < w j

/-- A nonpreemptive single-machine schedule, given by integer start times `S j`, is feasible
when no job starts before its release date and no two jobs overlap: job `j` occupies
`[S j, S j + p j)`. Idle time is allowed. The job type `ι` is any finite type, so that the
extended problem (E), whose jobs are the original jobs plus gap jobs, uses the same notion. -/
def IsFeasible {ι : Type*} (r p : ι → ℕ) (S : ι → ℕ) : Prop :=
  (∀ j, r j ≤ S j) ∧ ∀ i j, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i

/-- Total weighted completion time `∑ⱼ wⱼ Cⱼ` with `Cⱼ = S j + p j`. -/
noncomputable def cost {ι : Type*} [Fintype ι] (w : ι → ℝ) (p S : ι → ℕ) : ℝ :=
  ∑ j, w j * ((S j + p j : ℕ) : ℝ)

/-- `S` is an optimal (offline) schedule: feasible, and no feasible schedule has smaller
total weighted completion time. -/
def IsOptimal {ι : Type*} [Fintype ι] (r p : ι → ℕ) (w : ι → ℝ) (S : ι → ℕ) : Prop :=
  IsFeasible r p S ∧ ∀ S' : ι → ℕ, IsFeasible r p S' → cost w p S ≤ cost w p S'

end DelayedSWPT.Model
