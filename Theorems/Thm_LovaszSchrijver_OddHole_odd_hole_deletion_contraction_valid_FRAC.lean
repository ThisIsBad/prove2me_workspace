import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_OddHole
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction

namespace LovaszSchrijver.OddHole

/-- Part (1) of the proof of Theorem 2.3 (p. 178): for an odd hole `C` and any `i ∈ C`,
both the deletion and the contraction of `i` in the odd hole constraint
`∑_{j ∈ C} x_j ≤ (|C| − 1)/2` are valid for `FRAC(G)`. -/
theorem odd_hole_deletion_contraction_valid_FRAC {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) := by sorry

end LovaszSchrijver.OddHole
