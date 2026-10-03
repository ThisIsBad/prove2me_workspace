import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve

namespace TeschlODE.Stability

/-- Teschl, §6.2, p. 189, (6.8)–(6.9): `Φ` is the (local) flow of `ẋ = f(x)` on `M`, with
maximal time intervals `I x = (T₋(x), T₊(x))`. For every `x ∈ M`, the curve `t ↦ Φ t x` on
`I x` is an integral curve with `0 ∈ I x` and `Φ 0 x = x`, and it is the unique maximal one:
every integral curve `ψ` on an interval `J ∋ 0` with `ψ 0 = x` satisfies `J ⊆ I x` and agrees
with `Φ · x` on `J`. The flow's domain is `W = ⋃_{x ∈ M} I x × {x}`; values of `Φ t x` and
`I x` outside `W` (i.e. for `x ∉ M` or `t ∉ I x`) carry no meaning. -/
def IsMaximalFlow {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ M,
    IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ (0 : ℝ) ∈ I x ∧ Φ 0 x = x ∧
    ∀ (J : Set ℝ) (ψ : ℝ → EuclideanSpace ℝ (Fin n)),
      IsIntegralCurve f M J ψ → (0 : ℝ) ∈ J → ψ 0 = x → J ⊆ I x ∧ ∀ t ∈ J, ψ t = Φ t x

end TeschlODE.Stability
