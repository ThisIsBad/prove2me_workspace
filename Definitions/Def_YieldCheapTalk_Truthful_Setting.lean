import Mathlib

namespace YieldCheapTalk.Truthful
open MeasureTheory

/-- `T = M = {H, L}`: the supplier's types and the market states (§3, p. 6). -/
inductive Level
  | H
  | L
  deriving DecidableEq

instance : Fintype Level where
  elems := {Level.H, Level.L}
  complete := fun x => by cases x <;> simp

/-- §3, pp. 6–7: the primitives of the model. `a m` is the market potential `a_m`, `b` the slope of
the inverse demand `P(x|m) = a_m − b x`, `theta t` the mean yield `θ_t`, `delta` the common
coefficient of variation `δ`, `c` the unit production cost, `(w, eta)` the contract `(w, η)`,
`p t m` the joint probability `p_tm` of type `t` and state `m`, and `xi t` the law of the yield
`ξ_t`. -/
structure Model where
  a : Level → ℝ
  b : ℝ
  theta : Level → ℝ
  delta : ℝ
  c : ℝ
  w : ℝ
  eta : ℝ
  p : Level → Level → ℝ
  xi : Level → Measure ℝ

namespace Model
variable (M : Model)

/-- `µ(m|t) = p_tm / Σ_{m'} p_tm'`, the probability of state `m` given type `t` (p. 8). -/
noncomputable def mu (m t : Level) : ℝ := M.p t m / ∑ m', M.p t m'

/-- `λ(t|m) = p_tm / Σ_{t̂} p_t̂m`, the buyer's prior on type `t` given state `m` (p. 9). -/
noncomputable def lam (t m : Level) : ℝ := M.p t m / ∑ t', M.p t' m

/-- The standing assumptions of §3 (pp. 6–8) together with `a_H > a_L` (p. 12, "henceforth").
`b > 0` and `w > 0` are added (disclosed). The coefficient of variation `δ` of `ξ_t` is encoded,
as on p. 6, by the variance `σ_t² = δ² θ_t²`. -/
structure Standing : Prop where
  b_pos : 0 < M.b
  w_pos : 0 < M.w
  theta_lt : M.theta .L < M.theta .H
  isProb : ∀ t, IsProbabilityMeasure (M.xi t)
  support : ∀ t, ∀ᵐ x ∂(M.xi t), x ∈ Set.Icc (0 : ℝ) 1
  mean : ∀ t, ∫ x, x ∂(M.xi t) = M.theta t
  var : ∀ t, ∫ x, (x - M.theta t) ^ 2 ∂(M.xi t) = M.delta ^ 2 * M.theta t ^ 2
  eta_mem : M.eta ∈ Set.Icc (0 : ℝ) 1
  p_pos : ∀ t m, 0 < M.p t m
  p_sum : ∑ t, ∑ m, M.p t m = 1
  buyer_pos : ∀ m t, M.eta * M.w + (1 - M.eta) * M.w * M.theta t < M.a m * M.theta t
  supplier_pos : ∀ t, M.c < M.eta * M.w + (1 - M.eta) * M.w * M.theta t
  a_lt : M.a .L < M.a .H

/-- The buyer's expected profit from ordering `Q` when the yield has law `ν` and the market
potential is `a`: `E[ξQ(a − bξQ) − ηwQ − (1 − η)wξQ]`, the expectation inside (1). -/
noncomputable def profitYield (ν : Measure ℝ) (a Q : ℝ) : ℝ :=
  ∫ x, (x * Q * (a - M.b * (x * Q)) - M.eta * M.w * Q - (1 - M.eta) * M.w * x * Q) ∂ν

/-- (1), p. 7: `Π_B(Q|t', m) = Σ_t β(t|t', m) E_{ξ_t}[…]`, where `beta t t' m = β(t|t', m)`. -/
noncomputable def profitB (beta : Level → Level → Level → ℝ) (Q : ℝ) (t' m : Level) : ℝ :=
  ∑ t, beta t t' m * M.profitYield (M.xi t) (M.a m) Q

/-- (2), p. 8, with the base model's single unit cost `c`:
`Π_S(t'|t) = Σ_m µ(m|t) E_{ξ_t}[(ηw + (1 − η)wξ_t − c) Q*(t', m)]`, where `Q t' m = Q*(t', m)`. -/
noncomputable def profitS (Q : Level → Level → ℝ) (t' t : Level) : ℝ :=
  ∑ m, M.mu m t * ∫ x, (M.eta * M.w + (1 - M.eta) * M.w * x - M.c) * Q t' m ∂(M.xi t)

/-- The perfect Bayesian equilibrium of pp. 8–9: messaging strategy `r`, ordering strategy
`Q t' m = Q*(t', m)` and beliefs `beta t t' m = β(t|t', m)` satisfy (i) the supplier's
optimality, (ii) the buyer's optimality over all `Q ≥ 0`, and (iii) Bayes' rule on the
equilibrium path, with no restriction off path; beliefs are probability distributions on `T`. -/
def IsPBE (r : Level → Level) (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ) :
    Prop :=
  (∀ t t', M.profitS Q t' t ≤ M.profitS Q (r t) t) ∧
  (∀ t' m, 0 ≤ Q t' m ∧ ∀ Q', 0 ≤ Q' → M.profitB beta Q' t' m ≤ M.profitB beta (Q t' m) t' m) ∧
  (∀ t t' m, 0 ≤ beta t t' m) ∧ (∀ t' m, ∑ t, beta t t' m = 1) ∧
  (∀ t' m, 0 < ∑ s, (if r s = t' then (1 : ℝ) else 0) * M.lam s m →
    ∀ t, beta t t' m = (if r t = t' then (1 : ℝ) else 0) * M.lam t m /
      ∑ s, (if r s = t' then (1 : ℝ) else 0) * M.lam s m)

/-- (3), p. 10, as a closed form:
`Qʳ(θ, a) = ([a − (1 − η)w]θ − ηw) / (2b(1 + δ²)θ²)`. -/
noncomputable def Qr (θ a : ℝ) : ℝ :=
  ((a - (1 - M.eta) * M.w) * θ - M.eta * M.w) / (2 * M.b * (1 + M.delta ^ 2) * θ ^ 2)

/-- The IC condition (5), p. 11: for all `t ≠ t'`,
`Qʳ(θ_t, a_H)µ(H|t) + Qʳ(θ_t, a_L)µ(L|t) ≥ Qʳ(θ_t', a_H)µ(H|t) + Qʳ(θ_t', a_L)µ(L|t)`. -/
def IC5 : Prop := ∀ t t' : Level, t ≠ t' →
  M.Qr (M.theta t') (M.a .H) * M.mu .H t + M.Qr (M.theta t') (M.a .L) * M.mu .L t ≤
    M.Qr (M.theta t) (M.a .H) * M.mu .H t + M.Qr (M.theta t) (M.a .L) * M.mu .L t

end Model
end YieldCheapTalk.Truthful
