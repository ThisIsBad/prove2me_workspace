import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open MeasureTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Assumptions 2.3, 2.4 and 2.5(a) on a noise process `ξ_t` (`t ≥ 1`) in `ℝ^N`, on a filtered
probability space `(Ω, ℱ, ℱ_t, P)`. Conditioning on `ℱ_{t-1}` is written with the shifted index:
the noise `ξ (t+1)` given `ℱ t`.
* `ξ_t` is adapted and square integrable (so that the conditional moments below are defined);
* martingale difference: `E(ξ_t | ℱ_{t-1}) = 0` a.s. (Assumption 2.3);
* `sup_{t ≥ 1} E(|ξ_t|² | ℱ_{t-1}) < ∞` a.s. (Assumption 2.3);
* conditional Lindeberg (Assumption 2.4): `lim_{C→∞} limsup_{t→∞} E(|ξ_t|² I(|ξ_t| > C) | ℱ_{t-1}) = 0`
  in probability, unfolded as: for all `η, δ > 0` there is `C₀` such that for every `C ≥ C₀`,
  `P(E(|ξ_t|² I(|ξ_t| > C) | ℱ_{t-1}) > η for infinitely many t) ≤ δ`;
* conditional covariance (Assumption 2.5(a)): `E(ξ_t ξ_tᵀ | ℱ_{t-1}) → S` in probability,
  entrywise, and `S` is symmetric positive definite. -/
structure LinearNoiseAssumptions {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  adapted : Adapted ℱ ξ
  memLp : ∀ t, MemLp (ξ t) 2 P
  mds : ∀ t, P[ξ (t + 1) | ℱ t] =ᵐ[P] 0
  condVar_bdd : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t, P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω ≤ M
  lindeberg : ∀ η > 0, ∀ δ > 0, ∃ C₀ : ℝ, ∀ C ≥ C₀,
    P {ω | ∃ᶠ t in atTop, η < P[Set.indicator {ω' | C < ‖ξ (t + 1) ω'‖}
      (fun ω' => ‖ξ (t + 1) ω'‖ ^ 2) | ℱ t] ω} ≤ ENNReal.ofReal δ
  condCov : ∀ i j, TendstoInMeasure P
    (fun t ω => P[fun ω' => ξ (t + 1) ω' i * ξ (t + 1) ω' j | ℱ t] ω) atTop (fun _ => S i j)
  posDef : S.PosDef

/-- Assumption 3.1 (Lyapunov function), in the corrected form used by the proof of Theorem 2:
`V : ℝ^N → ℝ` is differentiable and there are `lam₁ > 0` (the paper's `λ`), `α > 0`, `ε > 0`,
`L > 0` with `V(x) ≥ α|x|²`, `|∇V(x) - ∇V(y)| ≤ L|x - y|`, `V(0) = 0` (printed `V(x*) = 0`),
`∇V(x - x*)ᵀ R(x) > 0` for `x ≠ x*`, and `∇V(x - x*)ᵀ R(x) ≥ lam₁ V(x - x*)` for `|x - x*| ≤ ε`
(printed `λ V(x)`). -/
def LyapunovAssumption {N : ℕ} (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (xstar : EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  Differentiable ℝ V ∧
  ∃ lam₁ α ε L : ℝ, 0 < lam₁ ∧ 0 < α ∧ 0 < ε ∧ 0 < L ∧
    (∀ x, α * ‖x‖ ^ 2 ≤ V x) ∧
    (∀ x y, ‖gradient V x - gradient V y‖ ≤ L * ‖x - y‖) ∧
    V 0 = 0 ∧
    (∀ x, x ≠ xstar → 0 < inner ℝ (gradient V (x - xstar)) (R x)) ∧
    (∀ x, ‖x - xstar‖ ≤ ε → lam₁ * V (x - xstar) ≤ inner ℝ (gradient V (x - xstar)) (R x))

/-- Assumption 3.2 (local linearisation): `0 < lam ≤ 1`, and there are `K₁` and `ε > 0` with
`|R(x) - G(x - x*)| ≤ K₁ |x - x*|^{1+lam}` for `|x - x*| ≤ ε`, and `Re λ_i(G) > 0` for every
eigenvalue of `G`. -/
def LinearizationAssumption {N : ℕ} (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (xstar : EuclideanSpace ℝ (Fin N)) (G : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ 1 ∧
  (∃ K₁ ε : ℝ, 0 < ε ∧ ∀ x, ‖x - xstar‖ ≤ ε →
    ‖R x - matApply G (x - xstar)‖ ≤ K₁ * ‖x - xstar‖ ^ (1 + lam)) ∧
  EigenRePos G

/-- Assumption 3.3 (noise), with the decomposition (9) `ξ_t = ξ_t(0) + ζ_t` where
`ξ0 t` is the paper's `ξ_t(0)` and `ζ_t = ξ_t - ξ0_t`. Here `x t = saIterate x₀ γ R ξ t` is the
iterate of Eq. (7), and conditioning on `ℱ_{t-1}` is written with the shifted index (`ξ (t+1)`
given `ℱ t`, next to the iterate `x t`).
* `ξ` and `ξ0` are adapted and square integrable;
* `E(ξ_t | ℱ_{t-1}) = 0` a.s. and, for some `K₂`,
  `E(|ξ_t|² | ℱ_{t-1}) + |R(x_{t-1})|² ≤ K₂ (1 + |x_{t-1}|²)` a.s., for all `t ≥ 1`;
* `E(ξ_t(0) | ℱ_{t-1}) = 0` a.s.; `E(ξ_t(0) ξ_t(0)ᵀ | ℱ_{t-1}) → S` in probability (entrywise),
  `S` symmetric positive definite;
* `sup_t E(|ξ_t(0)|² I(|ξ_t(0)| > C) | ℱ_{t-1}) → 0` in probability as `C → ∞`, unfolded as:
  for all `η, δ > 0` there is `C₀` such that for all `C ≥ C₀`,
  `P(∃ t ≥ 1, E(|ξ_t(0)|² I(|ξ_t(0)| > C) | ℱ_{t-1}) > η) ≤ δ`;
* for some `δ : ℝ^N → ℝ` with `δ(x) → 0` as `x → 0` and all `t` large enough,
  `E(|ζ_t|² | ℱ_{t-1}) ≤ δ(x_{t-1} - x*)` a.s. (printed `δ(x_{t-1})`). -/
structure NoiseAssumption {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (xstar : EuclideanSpace ℝ (Fin N))
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  adapted : Adapted ℱ ξ
  memLp : ∀ t, MemLp (ξ t) 2 P
  mds : ∀ t, P[ξ (t + 1) | ℱ t] =ᵐ[P] 0
  growth : ∃ K₂ : ℝ, ∀ t, ∀ᵐ ω ∂P,
    P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω + ‖R (saIterate x₀ γ R ξ t ω)‖ ^ 2
      ≤ K₂ * (1 + ‖saIterate x₀ γ R ξ t ω‖ ^ 2)
  adapted0 : Adapted ℱ ξ0
  memLp0 : ∀ t, MemLp (ξ0 t) 2 P
  mds0 : ∀ t, P[ξ0 (t + 1) | ℱ t] =ᵐ[P] 0
  condCov0 : ∀ i j, TendstoInMeasure P
    (fun t ω => P[fun ω' => ξ0 (t + 1) ω' i * ξ0 (t + 1) ω' j | ℱ t] ω) atTop (fun _ => S i j)
  posDef : S.PosDef
  lindeberg0 : ∀ η > 0, ∀ δ > 0, ∃ C₀ : ℝ, ∀ C ≥ C₀,
    P {ω | ∃ t, η < P[Set.indicator {ω' | C < ‖ξ0 (t + 1) ω'‖}
      (fun ω' => ‖ξ0 (t + 1) ω'‖ ^ 2) | ℱ t] ω} ≤ ENNReal.ofReal δ
  remainder : ∃ δ : EuclideanSpace ℝ (Fin N) → ℝ, Tendsto δ (𝓝 0) (𝓝 0) ∧
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ᵐ ω ∂P,
      P[fun ω' => ‖ξ (t + 1) ω' - ξ0 (t + 1) ω'‖ ^ 2 | ℱ t] ω ≤ δ (saIterate x₀ γ R ξ t ω - xstar)

/-- Assumption 3.4 (step sizes), with Eq. (10) in its intended form and two hypotheses the
proof of Theorem 2 uses added: `γ_t > 0` for `t ≥ 1`; `(γ_t - γ_{t+1})/γ_t = o(γ_t)`;
`∑_{t ≥ 1} γ_t^{(1+lam)/2} t^{-1/2} < ∞` (Eq. (10), printed `∑ (1+λ)/γ_t² t^{-1/2}`);
added: `γ_t → 0` and `∑_{t ≥ 1} γ_t² < ∞`. -/
def StepAssumption (γ : ℕ → ℝ) (lam : ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < γ t) ∧
  (fun t => (γ t - γ (t + 1)) / γ t) =o[atTop] γ ∧
  Summable (fun t : ℕ => γ (t + 1) ^ ((1 + lam) / 2) * ((t + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ∧
  Tendsto γ atTop (𝓝 0) ∧
  Summable (fun t : ℕ => γ (t + 1) ^ 2)

end PolyakJuditsky.Averaging
