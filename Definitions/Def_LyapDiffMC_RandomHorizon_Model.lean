import Mathlib
import Definitions.Def_MarkovChainKernel

namespace LyapDiffMC.RandomHorizon

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The data of §3 of Rhee–Glynn (arXiv:1707.03870v1, p. 8): a family `P θ` of one-step
transition (Markov) kernels on a measurable state space `S`, a reward `f : S → ℝ`, a discount
exponent `g : S → ℝ`, and a measurable nonempty set `C ⊆ S` whose complement is the target set
(`T = inf {n ≥ 0 : X n ∈ Cᶜ}`; `Cᶜ = ∅` is allowed, in which case `T = ∞`).
The family `P θ` is given for every `θ : ℝ`; only `θ ∈ Λ` is constrained by the theorems. -/
structure Setting (S : Type*) [MeasurableSpace S] where
  /-- the one-step transition kernel `P(θ)` -/
  P : ℝ → Kernel S S
  /-- each `P(θ)` is a Markov (probability) kernel -/
  markov : ∀ θ, IsMarkovKernel (P θ)
  /-- the reward `f` -/
  f : S → ℝ
  /-- the discount exponent `g` -/
  g : S → ℝ
  f_meas : Measurable f
  g_meas : Measurable g
  /-- the set `C`; the chain is stopped on first entrance to `Cᶜ` -/
  C : Set S
  C_meas : MeasurableSet C
  C_nonempty : C.Nonempty

attribute [instance] Setting.markov

variable {S : Type*} [MeasurableSpace S]

/-- The discounted kernel `K(θ, x, dy) = exp(g(x)) P(θ, x, dy)` (p. 9), on all of `S`.
Restricted to targets in `C` it is the kernel `K(θ)` on `C`; restricted to targets in `Cᶜ` it is
the kernel appearing in `f̃` (3.10) and in A3. (`Kernel.withDensity` of the measurable density
`exp ∘ g`, measurable by `g_meas`.) -/
noncomputable def discKernel (M : Setting S) (θ : ℝ) : Kernel S S :=
  (M.P θ).withDensity (fun x _ => ENNReal.ofReal (Real.exp (M.g x)))

/-- The non-negative kernel `K(θ) = (K(θ, x, dy) : x, y ∈ C)` of p. 9: `discKernel` with its
target restricted to `C`. -/
noncomputable def KC (M : Setting S) (θ : ℝ) : Kernel S S :=
  (discKernel M θ).restrict M.C_meas

/-- Powers of a kernel (p. 4): `Q⁰ = I` (`Q⁰(x, dy) = δₓ(dy)`) and `Qⁿ⁺¹ = Qⁿ Q`, i.e.
`Qⁿ⁺¹(x, A) = ∫ Qⁿ(x, dy) Q(y, A)`; Mathlib's `Q ∘ₖ η` first applies `η`, then `Q`, so the new
factor `Q` is applied last. This is the same kernel as the paper's `Qⁿ = Q Qⁿ⁻¹`. -/
noncomputable def Qpow (Q : Kernel S S) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n + 1 => Q ∘ₖ Qpow Q n

/-- `Kⁿ(θ)`, the `n`-th power of the kernel `K(θ)` on `C`. -/
noncomputable def kpow (M : Setting S) (θ : ℝ) (n : ℕ) : Kernel S S :=
  Qpow (KC M θ) n

/-- `G(θ, x, ·) = Σₙ Kⁿ(θ, x, ·)` ((3.9) at `θ₀`; possibly an infinite measure). -/
noncomputable def greenMeasure (M : Setting S) (θ : ℝ) (x : S) : Measure S :=
  Measure.sum (fun n => kpow M θ n x)

/-- `f̃(θ, x) = f(x) + ∫_{Cᶜ} K(θ, x, dy) f(y)` ((3.10), p. 10). A Bochner integral: it is the
paper's value when `f` is integrable on `Cᶜ` against `K(θ, x, ·)` (the theorems assume this). -/
noncomputable def ftilde (M : Setting S) (θ : ℝ) (x : S) : ℝ :=
  M.f x + ∫ y in M.Cᶜ, M.f y ∂(discKernel M θ x)

/-- `u*(θ, x) = Σₙ (Kⁿ(θ) f̃(θ))(x) = ∫ f̃(θ, y) G(θ, x, dy)`: the series representation
(2.2)/(3.6)/(3.8) of the random-horizon discounted expectation (3.1), which is the form the proof
of Theorem 3.1 (p. 12) works with. For `f ≥ 0` it equals the path expectation (3.1) by (3.8);
for signed `f` it is the reading adopted for this mission (the path expectation can be undefined
while the series converges absolutely). A Bochner integral (value `0` when `f̃(θ)` is not
`G(θ, x, ·)`-integrable; the theorems' hypotheses guarantee integrability). -/
noncomputable def uStar (M : Setting S) (θ : ℝ) (x : S) : ℝ :=
  ∫ y, ftilde M θ y ∂(greenMeasure M θ x)

/-- The exit time `T(ω) = inf {n ≥ 0 : ω n ∈ Cᶜ}` of a path `ω`, in `ℕ∞` (`⊤` if the path never
leaves `C`). -/
noncomputable def exitTime (M : Setting S) (ω : ℕ → S) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : ω n ∉ M.C), (n : ℕ∞)

/-- The `j`-th discounted reward `exp(Σ_{k<j} g(ω k)) f(ω j)` of a path, in `ℝ≥0∞`
(used only for `f ≥ 0`). -/
noncomputable def discReward (M : Setting S) (ω : ℕ → S) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range j, M.g (ω k)) * M.f (ω j))

/-- The random variable inside (3.1) for `f ≥ 0`:
`Σ_{j=0}^{T-1} exp(Σ_{k<j} g(X_k)) f(X_j) + exp(Σ_{k<T} g(X_k)) f(X_T)`, with the last term
absent on `{T = ∞}` (the infinite-horizon reading of p. 3). -/
noncomputable def pathReward (M : Setting S) (ω : ℕ → S) : ℝ≥0∞ :=
  (∑' j : ℕ, if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
    + (if exitTime M ω = ⊤ then 0 else discReward M ω (exitTime M ω).toNat)

/-- `f̃(θ, x)` in `ℝ≥0∞`, for `f ≥ 0`: `f(x) + ∫_{Cᶜ} K(θ, x, dy) f(y)`. -/
noncomputable def ftildeE (M : Setting S) (θ : ℝ) (x : S) : ℝ≥0∞ :=
  ENNReal.ofReal (M.f x) + ∫⁻ y in M.Cᶜ, ENNReal.ofReal (M.f y) ∂(discKernel M θ x)

/-- `k′(θ, x, y)`: the derivative of `θ ↦ k(θ, x, y)` within `[θ₀ - ε, θ₀ + ε]` (A2, A3); at
interior points the ordinary derivative, at the endpoints the one-sided one. -/
noncomputable def kder (k : ℝ → S → S → ℝ) (θ₀ ε θ : ℝ) (x y : S) : ℝ :=
  derivWithin (fun t => k t x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)) θ

/-- `ω_ε(x, y) = sup {|k′(θ, x, y)| : |θ - θ₀| < ε}` (p. 10), in `ℝ≥0∞`; for `y ∈ Cᶜ` this is
`ω̃_ε(x, y)` of A3 (the same formula). -/
noncomputable def omega (k : ℝ → S → S → ℝ) (θ₀ ε : ℝ) (x y : S) : ℝ≥0∞ :=
  ⨆ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ‖kder k θ₀ ε θ x y‖ₑ

/-- `r̃_ε(x) = ∫_{Cᶜ} ω̃_ε(x, y) |f(y)| K(θ₀, x, dy)` (A3, p. 10), in `ℝ≥0∞`. -/
noncomputable def rtilde (M : Setting S) (k : ℝ → S → S → ℝ) (θ₀ ε : ℝ) (x : S) : ℝ≥0∞ :=
  ∫⁻ y in M.Cᶜ, omega k θ₀ ε x y * ‖M.f y‖ₑ ∂(discKernel M θ₀ x)

end LyapDiffMC.RandomHorizon
