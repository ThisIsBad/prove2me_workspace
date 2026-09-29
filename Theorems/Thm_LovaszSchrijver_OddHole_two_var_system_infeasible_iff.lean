import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_AlternatingWalk

namespace LovaszSchrijver.OddHole

/-- Lemma 2.4 (p. 178): for a finite graph `H = (W, F)` with values `0 ≤ a(ij) ≤ b(ij)` on its
edges and `U ⊆ W`, the system `a(ij) ≤ yᵢ + yⱼ ≤ b(ij)` (ij ∈ F), `yᵢ ≥ 0` (i ∈ W),
`yᵢ = 0` (i ∈ U) has no solution iff there is a walk `v₀, …, v_p` of one of the types
(a)–(d). -/
theorem two_var_system_infeasible_iff {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (hab : ∀ e ∈ H.edgeSet, 0 ≤ a e ∧ a e ≤ b e) (U : Finset W) :
    (¬ ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0)) ↔
      ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧
        ((Odd p ∧ altB a b v < 0) ∨
         (Even p ∧ v 0 = v (Fin.last p) ∧ altB a b v < 0) ∨
         (Even p ∧ v (Fin.last p) ∈ U ∧ altB a b v < 0) ∨
         (Odd p ∧ v 0 ∈ U ∧ v (Fin.last p) ∈ U ∧ altA a b v < 0)) := by sorry

end LovaszSchrijver.OddHole
