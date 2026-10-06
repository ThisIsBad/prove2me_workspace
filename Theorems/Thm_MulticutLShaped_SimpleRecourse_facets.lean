import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- p. 389: each `Ψ_i` is the maximum of (at most) `J + 1` affine functions of `χ_i` (its facets),
and, `Ψ` being separable in `i`, `Ψ` is the maximum of (at most) `(J + 1)^{m2}` affine functions of
`χ`, indexed by the choices `σ : Fin m2 → Fin (J + 1)` of one facet per row. -/
theorem facets (inst : Instance n1 m1 m2 J) :
    ∃ a d : Fin m2 → Fin (J + 1) → ℝ,
      (∀ i (χi : ℝ), PsiI inst i χi =
        ((Finset.univ.sup' Finset.univ_nonempty fun l => a i l * χi + d i l : ℝ) : EReal)) ∧
      ∀ χ : Fin m2 → ℝ, Psi inst χ =
        ((Finset.univ.sup' Finset.univ_nonempty
          fun σ : Fin m2 → Fin (J + 1) => ∑ i, (a i (σ i) * χ i + d i (σ i)) : ℝ) : EReal) := by sorry

end MulticutLShaped.SimpleRecourse

