import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_Pairing

/-!
Megiddo, J. ACM 31 (1984), §3.2 p. 120 (Figure 2): a linearly dependent pair of hyperplanes of
opposite slopes has zero `x₁`-coefficients, and the hyperplane midway between them settles
the position of `x*` relative to one of the two. The paper's `x₁, x₂` are the indices `0, 1`
of `Fin (d + 2)`.
-/

namespace MegiddoLP.FixedDim

/-- **The linearly dependent pair.** Let `Hᵢ = {aᵢ ⬝ᵥ x = bᵢ}` have nonnegative slope and
`H_k = {a_k ⬝ᵥ x = b_k}` nonpositive slope, with `aᵢ = λ a_k` for a real `λ ≠ 0`. Then
`a_i1 = a_k1 = 0`, and there is a rule `F`, depending only on the data, mapping the oracle's
answer for the middle hyperplane `H⁽¹⁾_ik = {aᵢ ⬝ᵥ x = (bᵢ + λ b_k)/2}` to a choice of `Hᵢ`
(`true`) or `H_k` (`false`) and the correct position of `x` relative to it, for every `x`. -/
theorem dependent_pair {d : ℕ} (ai ak : Fin (d + 2) → ℝ) (bi bk lam : ℝ)
    (hlam : lam ≠ 0) (hdep : ai = lam • ak)
    (hi : HasNonnegSlope ai) (hk : HasNonposSlope ak) :
    (ai 0 = 0 ∧ ak 0 = 0) ∧
    ∃ F : Ordering → Bool × Ordering, ∀ x : Fin (d + 2) → ℝ,
      let r := F (compare (ai ⬝ᵥ x) ((bi + lam * bk) / 2))
      (r.1 = true → compare (ai ⬝ᵥ x) bi = r.2) ∧
      (r.1 = false → compare (ak ⬝ᵥ x) bk = r.2) := by sorry

end MegiddoLP.FixedDim
