import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2


namespace Disjunctive.CutCorrespondence

/-- Lemma 8.2 (Balas, *Disjunctive Programming*, §8.1, p. 98, [33]): let `(α,β,u,u0,v,v0)` be a
basic solution of `(CGLP)_k` (8.1) with `u0, v0 > 0`, and let the basic components of `u` and `v`
be indexed by `M1` and `M2` (`IsCGLPKBasis`: `α, β, u0, v0, u_{M1}, v_{M2}` are the basic
columns). Then `M1 ∩ M2 = ∅` and the `n×n` submatrix of `Ã` with rows `M1 ∪ M2` is nonsingular.

Corrected from the retired version, which only required `M1`, `M2` to *contain* the supports
of `u`, `v` (so `M1 = M2 = univ` was allowed); `M1`, `M2` are now the index sets of a genuine
basis. The section's standing assumption that `Ãx ≥ b̃` contains `x ≥ 0` and `x_j ≤ 1`
(`j ∈ N'`) is stated explicitly. -/
theorem basis_correspondence_v2 {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) :
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2) := by sorry

end Disjunctive.CutCorrespondence

