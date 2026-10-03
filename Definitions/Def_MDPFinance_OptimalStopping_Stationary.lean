import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.OptimalStopping

/-- The data of a **stationary stopping problem** (§10.1.5, p. 308, and §10.2, p. 309). -/
structure StationaryProblem (E : Type*) [MeasurableSpace E] where
  QX : E → Measure E
  QX_prob : ∀ x, IsProbabilityMeasure (QX x)
  QX_meas : Measurable QX
  c : E → ℝ
  c_meas : Measurable c
  g : E → ℝ
  g_meas : Measurable g
  beta : ℝ
  beta_mem : beta ∈ Set.Ioc (0 : ℝ) 1

variable {E : Type*} [MeasurableSpace E]

noncomputable def StationaryProblem.cyl (P : StationaryProblem E) :
    ℕ → (ℕ → Set E) → E → ℝ≥0∞
  | 0, _, _ => 1
  | (m + 1), B, x => ∫⁻ y in B 0, P.cyl m (fun i => B (i + 1)) y ∂(P.QX x)

/-- `Pr x` is the law of `(X_0, X_1, …)` given `X_0 = x`. -/
def StationaryProblem.IsPathLaw (P : StationaryProblem E) (Pr : E → Measure (ℕ → E)) : Prop :=
  (∀ x, IsProbabilityMeasure (Pr x)) ∧
  ∀ (x : E) (m : ℕ) (B : ℕ → Set E), (∀ i, MeasurableSet (B i)) →
    Pr x {w : ℕ → E | ∀ i ≤ m, w i ∈ B i}
      = (B 0).indicator (fun y => P.cyl m (fun i => B (i + 1)) y) x

/-- `R_τ := Σ_{k=0}^{τ-1} β^k c(X_k) + β^τ g(X_τ)` for `τ < ∞` (p. 309); `0` on `{τ = ∞}`. -/
noncomputable def StationaryProblem.reward (P : StationaryProblem E) (tau : (ℕ → E) → ℕ∞)
    (w : ℕ → E) : ℝ :=
  match tau w with
  | (m : ℕ) => (∑ k ∈ Finset.range m, P.beta ^ k * P.c (w k)) + P.beta ^ m * P.g (w m)
  | ⊤ => 0

/-- `𝔼_x[R_τ]` in `[-∞,∞]`. -/
noncomputable def StationaryProblem.EReward (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (tau : (ℕ → E) → ℕ∞) (x : E) : EReal :=
  erealIntegral (Pr x) (fun w => (P.reward tau w : EReal))

/-- `τ ∧ n`. -/
noncomputable def truncTime (tau : (ℕ → E) → ℕ∞) (n : ℕ) (w : ℕ → E) : ℕ∞ :=
  min (tau w) (n : ℕ∞)

/-- **Assumption (B)** (p. 309): for all `x`, `sup_{τ<∞} 𝔼_x[Σ_{k<τ} β^k c^+(X_k) + β^τ g^+(X_τ)]
< ∞` and `liminf_n 𝔼_x[R_{τ∧n}] ≥ 𝔼_x[R_τ]` for all a.s. finite `τ`. -/
def StationaryProblem.AssumptionB (P : StationaryProblem E) (Pr : E → Measure (ℕ → E)) : Prop :=
  (∀ x : E, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ tau : (ℕ → E) → ℕ∞, IsStopTime tau →
      (Pr x {w | tau w = ⊤} = 0) →
      ∫⁻ w, ENNReal.ofReal ((∑ k ∈ Finset.range ((tau w).toNat), P.beta ^ k * max (P.c (w k)) 0)
          + P.beta ^ (tau w).toNat * max (P.g (w (tau w).toNat)) 0) ∂(Pr x) ≤ C) ∧
  (∀ (x : E) (tau : (ℕ → E) → ℕ∞), IsStopTime tau → (Pr x {w | tau w = ⊤} = 0) →
      P.EReward Pr tau x ≤ liminf (fun n : ℕ => P.EReward Pr (truncTime tau n) x) atTop)

/-- **(B_N)** for the stationary `N`-stage problem. -/
def StationaryProblem.AssumptionBN (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (N : ℕ) : Prop :=
  ∀ x : E, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ tau : (ℕ → E) → ℕ∞, IsStopTime tau →
    (∀ w, tau w ≤ (N : ℕ∞)) →
    ∫⁻ w, ENNReal.ofReal ((∑ k ∈ Finset.range ((tau w).toNat), P.beta ^ k * max (P.c (w k)) 0)
        + P.beta ^ (tau w).toNat * max (P.g (w (tau w).toNat)) 0) ∂(Pr x) ≤ C

/-- `V_∞^*(x) := sup_{τ<∞} 𝔼_x[R_τ]` **(10.3)**, over stopping times finite a.s. -/
noncomputable def StationaryProblem.Vstar (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (x : E) : EReal :=
  ⨆ tau : (ℕ → E) → ℕ∞, ⨆ (_ : IsStopTime tau ∧ Pr x {w | tau w = ⊤} = 0), P.EReward Pr tau x

/-- The value of the **`n`-stage** stationary problem, `sup_{τ ≤ n} 𝔼_x[R_τ]` (p. 307). -/
noncomputable def StationaryProblem.valueUpTo (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (n : ℕ) (x : E) : EReal :=
  ⨆ tau : (ℕ → E) → ℕ∞, ⨆ (_ : IsStopTime tau ∧ ∀ w, tau w ≤ (n : ℕ∞)), P.EReward Pr tau x

/-- `τ^*` is **optimal** for the unbounded problem (p. 309): a stopping time, finite a.s., with
`V_∞^*(x) = 𝔼_x[R_{τ^*}]` for all `x`. -/
def StationaryProblem.IsOptimal (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (tau : (ℕ → E) → ℕ∞) : Prop :=
  IsStopTime tau ∧ (∀ x : E, Pr x {w | tau w = ⊤} = 0) ∧
    ∀ x : E, P.EReward Pr tau x = P.Vstar Pr x

/-- `T v(x) = max{g(x), c(x) + β ∫ v(x') Q^X(dx'|x)}` (Theorem 10.1.5 a)) in `[-∞,∞]`. -/
noncomputable def StationaryProblem.T (P : StationaryProblem E) (v : E → EReal) (x : E) : EReal :=
  max (P.g x : EReal) ((P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) v)

open Classical in
/-- `T_f v` for the decision rule `f = 1_S`: stop on `S`, continue off it. -/
noncomputable def StationaryProblem.Tf (P : StationaryProblem E) (S : Set E) (v : E → EReal)
    (x : E) : EReal :=
  if x ∈ S then (P.g x : EReal) else (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) v

/-- The value iteration `J_0 = g`, `J_n = T J_{n-1}`. -/
noncomputable def StationaryProblem.J (P : StationaryProblem E) : ℕ → E → EReal
  | 0 => fun x => (P.g x : EReal)
  | (n + 1) => P.T (P.J n)

/-- `J := lim_n J_n` (p. 310), the limit of the increasing sequence `(J_n)`. -/
noncomputable def StationaryProblem.Jlim (P : StationaryProblem E) (x : E) : EReal :=
  ⨆ n, P.J n x

/-- `d_n(x) := g(x) − c(x) − β ∫ J_{n-1}(x') Q^X(dx'|x)` (Theorem 10.1.5 c)), `n ≥ 1`. -/
noncomputable def StationaryProblem.d (P : StationaryProblem E) (n : ℕ) (x : E) : EReal :=
  (P.g x : EReal) - (P.c x : EReal) - (P.beta : EReal) * erealIntegral (P.QX x) (P.J (n - 1))

/-- `S_n^* := {x ∈ E | J_n(x) = g(x)}`. -/
def StationaryProblem.stopSet (P : StationaryProblem E) (n : ℕ) : Set E :=
  {x | P.J n x = (P.g x : EReal)}

/-- `v` is **`c`-superharmonic**: `v(x) ≥ c(x) + β ∫ v dQ^X(·|x)` (Theorem 10.2.2 c)). -/
def StationaryProblem.Superharmonic (P : StationaryProblem E) (v : E → EReal) : Prop :=
  ∀ x : E, (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) v ≤ v x

/-- `τ_f := inf{n | X_n ∈ S_f}` for the stationary rule `f = 1_S`. -/
noncomputable def StationaryProblem.ruleTime (_P : StationaryProblem E) (S : Set E) :
    (ℕ → E) → ℕ∞ :=
  hitTime S

/-- `G_f(x) := liminf_n J_{nf}(x) = liminf_n 𝔼_x[R_{τ_f ∧ n}]` (p. 310, 312), in `[-∞,∞]`. -/
noncomputable def StationaryProblem.Gf (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (S : Set E) (x : E) : EReal :=
  liminf (fun n : ℕ => P.EReward Pr (truncTime (P.ruleTime S) n) x) atTop

/-- `G_τ := liminf_n 𝔼_x[R_{τ∧n}]` for an arbitrary (history-dependent) stopping rule, and
`G(x) := sup_τ G_τ(x)` (p. 310; every stopping time is a history-dependent policy). -/
noncomputable def StationaryProblem.G (P : StationaryProblem E) (Pr : E → Measure (ℕ → E))
    (x : E) : EReal :=
  ⨆ tau : (ℕ → E) → ℕ∞, ⨆ (_ : IsStopTime tau),
    liminf (fun n : ℕ => P.EReward Pr (truncTime tau n) x) atTop

/-- `f = 1_S` is a **maximizer of** `v`: `T_f v = T v`. -/
def StationaryProblem.IsMaximizer (P : StationaryProblem E) (S : Set E) (v : E → EReal) : Prop :=
  MeasurableSet S ∧ ∀ x : E, P.Tf S v x = P.T v x

/-- A bounding function `b` with module `α_b` for the stopping Markov Decision Model
(Definition 7.1.1, restated): `b ≥ 0` measurable, `|c|, |g| ≤ c_r b`, `∫ b dQ^X(·|x) ≤ α_b b(x)`. -/
structure StationaryProblem.BoundingFunction (P : StationaryProblem E) where
  b : E → ℝ
  cr : ℝ
  alpha : ℝ
  b_nonneg : ∀ x, 0 ≤ b x
  b_meas : Measurable b
  cr_nonneg : 0 ≤ cr
  c_le : ∀ x, |P.c x| ≤ cr * b x
  g_le : ∀ x, |P.g x| ≤ cr * b x
  drift : ∀ x, ∫⁻ y, ENNReal.ofReal (b y) ∂(P.QX x) ≤ ENNReal.ofReal (alpha * b x)

end MDPFinance.OptimalStopping
