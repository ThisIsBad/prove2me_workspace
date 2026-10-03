import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp

namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.9 (Balas §11.5, p. 162): let `(α,β,{uᵗ,uᵗ₀})` be a feasible solution to the CGLP
(11.6) with `uᵗ₀>0` for every `t`. If there is a nonsingular `n×n` submatrix `Ã_ι` of `Ã` (an
injective cobasis `ι`) such that every `uᵗ` vanishes off the image of `ι`, then the L&P cut
`αx≥β` is equivalent to the intersection cut `πx_J≥1` from `S` and the LP simplex tableau with
nonbasic set `ι`. -/
theorem lp_cut_equals_intersection_cut {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hfeas : IsCGLP116Feasible Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0) :
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0 := by sorry

end Disjunctive.GeneralDisjunctions

