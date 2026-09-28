import Mathlib

namespace SpectralProjGrad.Shared

/-- `P` is the orthogonal (Euclidean) projection onto `Ω ⊆ ℝⁿ`: for every `z`, the point `P z`
lies in `Ω` and is a point of `Ω` nearest to `z` in the Euclidean norm. (For a nonempty closed
convex `Ω` such a nearest point exists and is unique, so this characterizes `P`.) -/
def IsProjOnto {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n), P z ∈ Ω ∧ ∀ y ∈ Ω, ‖z - P z‖ ≤ ‖z - y‖

end SpectralProjGrad.Shared
