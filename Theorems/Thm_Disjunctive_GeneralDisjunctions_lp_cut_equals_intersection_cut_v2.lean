import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp_v2


namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.9 (Balas, *Disjunctive Programming*, §11.5, p. 162; Balas–Kis 2016, Theorem 9):
let `(α, β, {uᵗ, uᵗ₀})` be a basic feasible solution of the CGLP (11.6) with `uᵗ₀ > 0` for all
`t ∈ T`. If there is a nonsingular `n×n` submatrix `Ã_J` of `Ã` (rows `ι`) such that `uᵗ_j = 0`
for all `j ∉ J`, `t ∈ T`, then the L&P cut `αx ≥ β` is equivalent to the intersection cut
`πx_J ≥ 1` from `S = {x : dᵗx ≤ dᵗ₀, t ∈ T}` and the LP simplex tableau with nonbasic set `J`
(expressed through the surplus variables `x_J = s_J(x)` of the rows `ι`).

Corrected from the retired version: the solution is *basic* (an extreme point of (11.6)), not
merely feasible (a feasible solution does not determine the cut); and the intersection cut from
`S` and the tableau of `J` is only defined when the basic solution `ā0` lies in `int S`
(`BasicSolutionInIntS`, the standing requirement of Theorem 1.1 used in the book's proof: "the
right-hand side is positive since `ā0 ∈ int S`"). -/
theorem lp_cut_equals_intersection_cut_v2 {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0)
    (hint : BasicSolutionInIntS Atil btil ι d d0) :
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0 := by sorry

end Disjunctive.GeneralDisjunctions

