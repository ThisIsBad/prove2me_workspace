import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.4B (Balas §8.1, p. 101-102), the converse of Theorem 8.4A: given any nonsingular
`n×n` submatrix `Â` of `Ã` (enumerated by `ι`) with `0 < ā_k0 < 1`, and a partition `(M1,M2)` of
its row set assigning `ι i` to `M1` when `π¹_i < π²_i` and to `M2` when `π¹_i > π²_i`, there is a
basic feasible solution to `(CGLP)_k` with `u0,v0>0` and basic `u`/`v` components indexed by
`M1`/`M2`, whose lift-and-project cut `αx ≥ β` is equivalent to the simple disjunctive cut from
`Â`. -/
theorem simple_disj_cut_eq_lp_cut {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (ι : Fin n → M) (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (h0 : 0 < Abar0 Atil btil ι k) (h1 : Abar0 Atil btil ι k < 1) (M1 M2 : Finset M)
    (hpart : ∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
      (Pi1 Atil btil ι k i > Pi2 Atil btil ι k i → ι i ∈ M2)) :
    ∃ α u u0 v v0 β, IsCGLPKFeasible Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
      (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧
      {x | β ≤ dotProduct α x} = SimpleDisjCutSet Atil btil ι k := by sorry

end Disjunctive.CutCorrespondence

