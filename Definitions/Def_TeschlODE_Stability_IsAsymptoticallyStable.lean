import Mathlib
import Definitions.Def_TeschlODE_Stability_IsStable

namespace TeschlODE.Stability

/-- Teschl, §6.5, p. 198, (6.26): the fixed point `x₀` is asymptotically stable: it is stable
and there is a neighborhood `U ⊆ M` of `x₀` such that for every `x ∈ U` the solution exists for
all `t ≥ 0` and `Φ(t, x) → x₀` as `t → ∞` (i.e. `|Φ(t, x) - x₀| → 0`). -/
def IsAsymptoticallyStable {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsStable M I Φ x₀ ∧
  ∃ U ∈ nhds x₀, U ⊆ M ∧ ∀ x ∈ U, (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
    Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds x₀)

end TeschlODE.Stability
