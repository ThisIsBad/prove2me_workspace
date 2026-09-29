import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

/-- The last observation time before `t`: `δ_t = [t/τ] τ`, where `[t/τ]` is the integer part
of `t/τ ≥ 0`. -/
noncomputable def delta (τ t : ℝ≥0) : ℝ≥0 := (⌊t / τ⌋₊ : ℝ≥0) * τ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `x` is a solution of the controlled hybrid SDE (2.1),
`dx(t) = (f(x(t), r(t), t) + u(x(δ_t), r(t), t)) dt + g(x(t), r(t), t) dw(t)`, `x(0) = x₀`,
on `t ≥ 0`, driven by the stochastic basis `S` (the diffusion `g` is given by its `m` columns;
column `k` multiplies `dw_k`):

* `x` is progressively measurable for `{𝓕_t}`;
* almost every path `t ↦ x(t, ω)` is continuous;
* `E|x(t)|² < ∞` for every `t ≥ 0`;
* there are Itô integral processes `J_k(t) = ∫₀ᵗ g_k(x(s), r(s), s) dw_k(s)`, `k = 1, …, m`, and
  for every `t ≥ 0`, almost surely, the drift `s ↦ f(x(s), r(s), s) + u(x(δ_s), r(s), s)` is
  Lebesgue integrable on `[0, t]` and
  `x(t) = x₀ + ∫₀ᵗ (f(x(s), r(s), s) + u(x(δ_s), r(s), s)) ds + ∑_k J_k(t)`. -/
def SolvesSampledHybridSDE {P : Measure Ω} {n m N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℝ}
    {r₀ : Fin N} (S : HybridSetup P m N Γ r₀)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (τ : ℝ≥0) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsStronglyProgressive S.𝓕 x ∧
    (∀ᵐ ω ∂P, Continuous (fun t => x t ω)) ∧
    (∀ t : ℝ≥0, ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P < ⊤) ∧
    ∃ J : Fin m → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n),
      (∀ k, IsItoIntegral P S.𝓕 (fun t ω => S.w t ω k)
          (fun s ω => g (x s ω) (S.r s ω) s k) (J k)) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        IntegrableOn (fun s : ℝ => f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal
            + u (x (delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal)
          (Set.Icc 0 (t : ℝ)) ∧
        x t ω = x₀ + (∫ s in Set.Icc (0 : ℝ) t,
            (f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal
              + u (x (delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal))
          + ∑ k, J k t ω

end You2015.Shared
