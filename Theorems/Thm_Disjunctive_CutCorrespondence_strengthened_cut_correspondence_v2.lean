import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2


namespace Disjunctive.CutCorrespondence

/-- Theorem 8.5 (Balas, *Disjunctive Programming*, §8.2, p. 103): Theorems 8.4A and 8.4B remain
valid if the lift-and-project cut `αx ≥ β` is replaced by the strengthened lift-and-project cut
`γx ≥ β` of Theorem 6.4 and the simple disjunctive cut `π^s_J x_J ≥ π0` by the mixed integer
Gomory cut `π̄^s_J x_J ≥ π0` of eq. (8.10).

(A) [8.4A strengthened] For a basic solution of `(CGLP)_k` with `u0, v0 > 0` whose basic
`u`/`v`-components are indexed by `M1`/`M2`, and any enumeration `ι` of `J := M1 ∪ M2`, the
halfspace `γx ≥ β` equals the MIG cut from the tableau row of `x_k` with nonbasic set `J`.

(B) [8.4B strengthened] Conversely, for every nonsingular `Â = Ã_J` (enumerated by `ι`) with
`0 < ā_k0 < 1` and every partition `(M1, M2)` of `J` putting `j` into `M1` when `π¹_j < π²_j` and
into `M2` when `π¹_j > π²_j`, there is a basic solution of `(CGLP)_k` with `u0, v0 > 0` and basic
`u`/`v`-components indexed by `M1`/`M2` whose strengthened cut `γx ≥ β` equals that MIG cut.

Corrected from the retired version: (i) `PiBar` now strengthens exactly the nonbasic positions
whose row is the bound `x_j ≥ 0` of a 0-1 variable `j ∈ N'` ("`j ∈ J ∩ N'`"), not the row
positions numbered by `N'`; (ii) `Gamma` removes the multipliers of the rows `x_j ≥ 0` from
`uÃ_j, vÃ_j` as Theorem 6.4 requires (the retired `Gamma` coincided with `α` at every feasible
point); (iii) `M1, M2` are the index sets of a basis (`IsCGLPKBasis`); (iv) the converse part
(B) of Theorem 8.5 is included; (v) the standing assumption that `Ãx ≥ b̃` contains `x ≥ 0` and
`x_j ≤ 1` (`j ∈ N'`) is explicit. -/
theorem strengthened_cut_correspondence_v2 {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n) :
    (∀ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
        (ι : Fin n → M),
      IsBasicCGLPKSolution Atil btil k α u u0 v v0 β → 0 < u0 → 0 < v0 →
      (∀ ρ ∉ M1, u ρ = 0) → (∀ ρ ∉ M2, v ρ = 0) → IsCGLPKBasis Atil btil k M1 M2 →
      Function.Injective ι → Finset.image ι Finset.univ = M1 ∪ M2 →
      {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
        StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) ∧
    (∀ (ι : Fin n → M) (M1 M2 : Finset M),
      Function.Injective ι → IsUnit (Ahat Atil ι).det →
      0 < Abar0 Atil btil ι k → Abar0 Atil btil ι k < 1 →
      Disjoint M1 M2 → M1 ∪ M2 = Finset.image ι Finset.univ →
      (∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
        (Pi2 Atil btil ι k i < Pi1 Atil btil ι k i → ι i ∈ M2)) →
      ∃ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ),
        IsBasicCGLPKSolution Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
        (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧ IsCGLPKBasis Atil btil k M1 M2 ∧
        {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
          StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) := by sorry

end Disjunctive.CutCorrespondence

