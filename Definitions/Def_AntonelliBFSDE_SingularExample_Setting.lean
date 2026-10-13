import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The norm of `L¹(μ)` for `μ = dt ⊗ dP` on `(0, T] × Ω`:
`E(∫_0^T |V_t| dt)`, as an iterated lower integral in `[0, ∞]`. -/
noncomputable def L1NormDt (P : Measure Ω) (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ r in Set.Ioc (0 : ℝ) (T : ℝ), ‖V r.toNNReal ω‖ₑ ∂volume ∂P

/-- `V ∈ L¹(μ)` for `μ = dt ⊗ dP`: `V` is jointly measurable on `[0,T] × Ω` and
`E(∫_0^T |V_t| dt) < ∞`. -/
def MemL1Dt (P : Measure Ω) (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) ∧
    L1NormDt P T V < ⊤

/-- The random variable inside the conditional expectation of (3.2) with `C_s = s`:
`ξ_t = ∫_t^T g(U_s, V_s) ds + Y`, the integral taken over `(t, T]`. -/
noncomputable def xiDt (T : ℝ≥0) (g : ℝ → ℝ → ℝ) (Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ s in Set.Ioc (t : ℝ) (T : ℝ), g (U s.toNNReal ω) (V s.toNNReal ω)) + Y ω

/-- `(U, V)` solves the system (3.1)–(3.2) with `A_s = C_s = s`, `J_t ≡ J₀` and deterministic
coefficients `f, g`, where `μ = dt ⊗ dP`:
`U, V ∈ L¹(μ)` and are adapted; their coefficient paths are integrable almost surely;
each `ξ_t = ∫_t^T g(U_s, V_s) ds + Y` (`t ≤ T`) is integrable; and for some
jointly measurable version `W` of `t ↦ E(ξ_t | 𝓕_t)`,
`U_t = J₀ + ∫_0^t f(U_s, V_s) ds` and `V_t = W_t` hold `P`-a.s. at each time;
the terminal value is `V_T = Y` almost surely. -/
def IsDtSystemSolution (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (J₀ : Ω → ℝ)
    (f g : ℝ → ℝ → ℝ) (Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) : Prop :=
  MemL1Dt P T U ∧ MemL1Dt P T V ∧
  (∀ t ≤ T, Measurable[𝓕 t] (U t)) ∧ (∀ t ≤ T, Measurable[𝓕 t] (V t)) ∧
  (∀ᵐ ω ∂P,
    IntegrableOn (fun s : ℝ => f (U s.toNNReal ω) (V s.toNNReal ω))
      (Set.Ioc (0 : ℝ) (T : ℝ)) volume ∧
    IntegrableOn (fun s : ℝ => g (U s.toNNReal ω) (V s.toNNReal ω))
      (Set.Ioc (0 : ℝ) (T : ℝ)) volume) ∧
  (∀ t ≤ T, Integrable (xiDt T g Y U V t) P) ∧
  ∃ W : ℝ≥0 → Ω → ℝ, AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (xiDt T g Y U V) W ∧
    (∀ t ≤ T,
      U t =ᵐ[P] (fun ω =>
        J₀ ω + ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), f (U s.toNNReal ω) (V s.toNNReal ω)) ∧
      V t =ᵐ[P] W t) ∧
    V T =ᵐ[P] Y

end AntonelliBFSDE.SingularExample
