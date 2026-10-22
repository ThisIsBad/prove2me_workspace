import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace SelfDualLP.Regularity

/-- The paper's (LP), in the published standard-form representation. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)

/-- The paper's (LD), `max bᵀy` subject to `Aᵀy ≤ c`, with `y` free. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  y ∈ LinearOptimization.dualFeasibleStd A c

/-- Interior feasibility of (LP): `Ax = b` and every `xⱼ > 0`. -/
def PrimalInterior {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- Interior feasibility of (LD): every slack `cⱼ - (Aᵀy)ⱼ > 0`. -/
def DualInterior {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ j, 0 < c j - (Aᵀ *ᵥ y) j

end SelfDualLP.Regularity
