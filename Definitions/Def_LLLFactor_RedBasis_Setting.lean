import Mathlib

namespace LLLFactor.RedBasis
noncomputable section

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def gs {n : ℕ} (b : Fin n → Vec n) (i : Fin n) : Vec n :=
  InnerProductSpace.gramSchmidt ℝ b i

def mu {n : ℕ} (b : Fin n → Vec n) (i j : Fin n) : ℝ :=
  inner ℝ (b i) (gs b j) / inner ℝ (gs b j) (gs b j)

def latticeOf {n : ℕ} (b : Fin n → Vec n) : Submodule ℤ (Vec n) :=
  Submodule.span ℤ (Set.range b)

def IsBasisFor {n : ℕ} (b : Fin n → Vec n) (L : Submodule ℤ (Vec n)) : Prop :=
  LinearIndependent ℝ b ∧ latticeOf b = L

def latticeDet {n : ℕ} (b : Fin n → Vec n) : ℝ :=
  |Matrix.det (Matrix.of fun i j => b j i)|

def IsReduced {n : ℕ} (b : Fin n → Vec n) : Prop :=
  (∀ i j : Fin n, j < i → |mu b i j| ≤ (1 / 2 : ℝ)) ∧
  (∀ (i : ℕ) (hi : i + 1 < n),
    (3 / 4 : ℝ) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
      ‖gs b ⟨i + 1, hi⟩ + mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ • gs b ⟨i, by omega⟩‖ ^ 2)

end
end LLLFactor.RedBasis
