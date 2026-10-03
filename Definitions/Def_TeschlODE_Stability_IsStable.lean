import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.5, p. 198: the fixed point `x₀` is (Liapunov) stable for the flow `Φ` (with
maximal time intervals `I`) on `M`: for every neighborhood `U` of `x₀` there is a neighborhood
`V ⊆ U` of `x₀`, contained in `M`, such that the solution starting at any `x ∈ V` exists for all
`t ≥ 0` and remains in `U` for all `t ≥ 0`. -/
def IsStable {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ U ∈ nhds x₀, ∃ V ∈ nhds x₀, V ⊆ U ∧ V ⊆ M ∧
    ∀ x ∈ V, ∀ t : ℝ, 0 ≤ t → t ∈ I x ∧ Φ t x ∈ U

end TeschlODE.Stability
