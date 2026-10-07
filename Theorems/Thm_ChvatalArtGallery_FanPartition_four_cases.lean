import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40, cases (1)–(4): a (k + 1)-triangulation G₁ (4 ≤ k ≤ 6, vertices
0, …, k, cut edge (0, k) on its boundary) all of whose inner edges (a, b), a < b, have b − a ≤ 3
is a fan, or is one of the configurations (2), (3), (4), or the mirror image (i ↦ k − i) of (2)
or (4). -/
theorem four_cases (k : ℕ) (hk4 : 4 ≤ k) (hk6 : k ≤ 6) (D₁ : Finset (Sym2 (Fin (k + 1))))
    (hD₁ : IsTriangulation (k + 1) D₁)
    (hspan : ∀ a b : Fin (k + 1), a < b → s(a, b) ∈ D₁ → b.val - a.val ≤ 3) :
    IsFan (k + 1) D₁ (triangles (k + 1) D₁) ∨
    (k = 5 ∧ (D₁ = {s(0, 2), s(0, 3), s(3, 5)} ∨
      D₁.image (Sym2.map Fin.rev) = {s(0, 2), s(0, 3), s(3, 5)})) ∨
    (k = 6 ∧ D₁ = {s(0, 2), s(0, 3), s(3, 6), s(4, 6)}) ∨
    (k = 6 ∧ (D₁ = {s(0, 3), s(1, 3), s(3, 6), s(4, 6)} ∨
      D₁.image (Sym2.map Fin.rev) = {s(0, 3), s(1, 3), s(3, 6), s(4, 6)})) := by sorry

end ChvatalArtGallery.FanPartition

