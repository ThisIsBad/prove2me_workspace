import Mathlib
import Definitions.Def_FoundationsML_Stability_EmpiricalError

namespace StabGen.RKHS

open FoundationsML.Stability

/-- The range of predictions made by functions in `F`, denoted `D` in Definition 19. -/
def predictionDomain {X : Type*} (F : Set (X → ℝ)) : Set ℝ :=
  {a | ∃ f ∈ F, ∃ x : X, f x = a}

/-- Definition 19, p. 512: convexity of the cost in its prediction argument and a
uniform Lipschitz bound on the predictions attainable in `F`. A Lipschitz constant
is nonnegative, including when the prediction domain is a singleton or empty. -/
def SigmaAdmissible {X Y : Type*} (F : Set (X → ℝ))
    (c : ℝ → Y → ℝ) (σ : ℝ) : Prop :=
  0 ≤ σ ∧
  (∀ y : Y, ConvexOn ℝ Set.univ (fun a : ℝ => c a y)) ∧
  ∀ a ∈ predictionDomain F, ∀ b ∈ predictionDomain F, ∀ y : Y,
    |c a y - c b y| ≤ σ * |a - b|

/-- Equation (19): empirical loss with normalization `1/m`, plus regularization. -/
noncomputable def regRisk {X Y H : Type*} {m : ℕ} (c : ℝ → Y → ℝ)
    (ev : H → X → ℝ) (S : Fin m → X × Y) (lam : ℝ) (N : H → ℝ)
    (g : H) : ℝ :=
  EmpiricalError c S (ev g) + lam * N g

/-- Equation (20): remove observation `i` while retaining the normalization `1/m`. -/
noncomputable def truncRegRisk {X Y H : Type*} {m : ℕ} (c : ℝ → Y → ℝ)
    (ev : H → X → ℝ) (S : Fin m → X × Y) (i : Fin m)
    (lam : ℝ) (N : H → ℝ) (g : H) : ℝ :=
  (1 / (m : ℝ)) * ∑ j ∈ Finset.univ.erase i, Loss c (ev g) (S j) + lam * N g

end StabGen.RKHS
