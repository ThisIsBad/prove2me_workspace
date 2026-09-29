import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace GeneralCK

/-- The Boolean cube `{0,1}^n`, as functions `Fin n → Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Binary entropy in bits, including the continuous endpoint values. -/
noncomputable def H (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Independent coordinate bit flips. `p` is crossover, not correlation. -/
noncomputable def noiseKernel {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - p else p

/-- The joint mass of `(f(X),Y)` for uniform `X` and binary symmetric noise. -/
noncomputable def jointMass {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then noiseKernel p x y else 0

/-- Finite Shannon entropy in bits. Used below only for probability masses. -/
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (q a)) / Real.log 2

/-- Mutual information from joint and marginal finite masses. -/
noncomputable def mutualInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointMass f p b y) +
  entropy (fun y => ∑ b, jointMass f p b y) -
  entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2)

/-- Review target: all dimensions (including zero), all Boolean functions,
all crossover probabilities (including zero, one half, and one).
This is a proposition definition, not an asserted theorem. -/
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p

end GeneralCK
