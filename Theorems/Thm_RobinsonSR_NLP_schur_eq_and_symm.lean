import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Proof of Theorem 4.1, p. 56: if the matrix (4.5) is nonsingular, the equations (4.8)
`ℒ″V + HᵀA + G⁺ᵀB = G⁰ᵀ, −HV = 0, −G⁺V = 0` have exactly one solution `(V, A, B)`; for it the
Schur complement (4.6) satisfies `S = G⁰V`, and, `ℒ″` being symmetric, `S = VᵀℒʺV`; hence `S` is
symmetric. -/
theorem schur_eq_and_symm {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hK : (kktMatrix Q H Gp).det ≠ 0) (hQ : Q.IsSymm) :
    (∃! VAB : Matrix ιn ιs ℝ × Matrix ιq ιs ℝ × Matrix ιr ιs ℝ,
        Q * VAB.1 + Hᵀ * VAB.2.1 + Gpᵀ * VAB.2.2 = G0ᵀ ∧ -H * VAB.1 = 0 ∧ -Gp * VAB.1 = 0) ∧
    (∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
        Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ → -H * V = 0 → -Gp * V = 0 →
          schurS Q H Gp G0 = G0 * V ∧ schurS Q H Gp G0 = Vᵀ * Q * V) ∧
    (schurS Q H Gp G0).IsSymm := by sorry

end RobinsonSR.NLP

