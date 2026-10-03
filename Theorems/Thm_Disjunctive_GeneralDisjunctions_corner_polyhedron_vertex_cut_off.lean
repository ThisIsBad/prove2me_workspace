import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner

namespace Disjunctive.GeneralDisjunctions

/-- Corollary 11.3 (Balas §11.2, p. 152): every vertex `v` of a corner polyhedron `corner(J)`
(apex `w`, basic index set `I`, cobasis `J`, integrality set `Nprime`) such that `v ∉ conv(P_I)`
is cut off by some standard intersection cut, i.e. `v` is itself a basic solution (for some fresh
basic/nonbasic pair `I',J'` and tableau `abar'`) lying in the interior of some `P_I`-free convex
set `S` **whose intersection cut is valid for `P_I` and cuts `v` off**. Without those two
clauses the statement is satisfied by `J' = ∅` and a small ball around `v`, and names no cut. -/
theorem corner_polyhedron_vertex_cut_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (w : ι → ℝ) (Nprime : Finset ι) (PI : Set (ι → ℝ))
    (v : ι → ℝ) (hv : v ∈ Set.extremePoints ℝ (cornerPolyhedron I J abar w Nprime))
    (hvPI : v ∉ convexHull ℝ PI) :
    ∃ (I' J' : Finset ι) (abar' : ι → ι → ℝ) (S : Set (ι → ℝ)) (lam : ι → ℝ),
      (∀ j ∈ J', v j = 0) ∧ PIFree S PI v ∧
        (∀ j ∈ J', IsGreatest {t : ℝ | v + t • extremeRay I' abar' j ∈ S} (lam j)) ∧
        PI ⊆ IntersectionCutSet J' lam ∧ v ∉ IntersectionCutSet J' lam := by sorry

end Disjunctive.GeneralDisjunctions

