import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Lemma 2. Let `Ω` be the solution set of `Ax ≤ b`, `x ∉ Ω`, and `y` a
point of `Ω` nearest to `x` (Euclidean). Let `S` be the set of half spaces whose bounding
hyperplane contains `y` and `Ω_S` their intersection. Then `x ∉ Ω_S` and `y` is a nearest point
of `Ω_S` to `x`. -/
theorem lemma2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : x ∉ solutionSet A b) (hy : IsNearest (solutionSet A b) x y) :
    x ∉ {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} ∧
      IsNearest {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} x y := by sorry

end HoffmanBound.ErrorBound

