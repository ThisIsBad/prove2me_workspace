import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem algebraicSet_radicalIdeal_correspondence {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} :
    Set.BijOn (zeroSet (K := K) (n := n)) {J | J.IsRadical} {W | IsAlgebraicSet W} ∧
    (∀ J₁ J₂ : Ideal (MvPolynomial (Fin n) K), J₁ ≤ J₂ → zeroSet J₂ ⊆ zeroSet J₁) ∧
    (∀ J : Ideal (MvPolynomial (Fin n) K), J.IsRadical → vanishingIdeal (zeroSet J) = J) ∧
    (∀ W : Set (Fin n → K), IsAlgebraicSet W → zeroSet (vanishingIdeal W) = W) := by sorry

end Nullstellensatz
