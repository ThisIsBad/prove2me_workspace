import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

/-!
Megiddo, J. ACM 31 (1984), §3.2 pp. 119–120 (Figure 1): if `Hᵢ` has nonnegative slope and
`H_k` nonpositive slope, then the positions of `x*` relative to `H⁽¹⁾_ik` and `H⁽²⁾_ik`
determine its position relative to one of `Hᵢ`, `H_k`. The paper's `x₁, x₂` are the indices
`0, 1` of `Fin (d + 2)`.
-/

namespace MegiddoLP.FixedDim

/-- **The pairing claim.** Let `Hᵢ = {aᵢ ⬝ᵥ x = bᵢ}` have nonnegative slope and
`H_k = {a_k ⬝ᵥ x = b_k}` nonpositive slope in the `(x₁, x₂)` plane, with
`a_k1 a_i2 - a_k2 a_i1 ≠ 0`. There is a rule `F`, depending only on the data, which maps the
oracle's answers for `H⁽¹⁾_ik` and `H⁽²⁾_ik` to a choice of `Hᵢ` (`true`) or `H_k` (`false`)
together with the correct position of `x` relative to the chosen hyperplane, for every `x`. -/
theorem pair_opposite_slopes {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk : ℝ)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak)
    (hdet : ak 0 * ai 1 - ak 1 * ai 0 ≠ 0) :
    ∃ F : Ordering → Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (pairNormal1 ai ak ⬝ᵥ x) (pairRhs1 ai ak bi bk))
                 (compare (pairNormal2 ai ak ⬝ᵥ x) (pairRhs2 ai ak bi bk))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by sorry

end MegiddoLP.FixedDim
