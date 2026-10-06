import Mathlib

namespace FedergruenZipkin.AvgCost

open scoped ENNReal
open Filter Topology

/-- The capacitated periodic-review inventory model of Federgruen and Zipkin (1986), §2,
pp. 195–196, with its standing Assumptions 1–4. The per-unit order cost `c` is absent: the paper
sets `c = 0` without loss of generality (p. 195). The storage capacity `U` is not a field; it is an
explicit parameter of every definition and theorem. -/
structure Model where
  /-- `p j = Pr{D = j}`, the probability mass function of the one-period demand `D` -/
  p : ℕ → ℝ
  p_nonneg : ∀ j, 0 ≤ p j
  p_sum : HasSum p 1
  /-- Assumption 2: the characteristic function `θ ↦ E e^{iθD}` is analytic at the origin -/
  charfun_analytic : AnalyticAt ℝ
    (fun θ : ℝ => ∑' j : ℕ, ((p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))) 0
  /-- `0 < μ = E(D)` (p. 195) -/
  mean_pos : 0 < ∑' j : ℕ, (j : ℝ) * p j
  /-- `b`, the production capacity (limit on order size), a positive integer -/
  b : ℕ
  b_pos : 0 < b
  /-- Assumption 4(a): `b > μ` -/
  mean_lt_b : ∑' j : ℕ, (j : ℝ) * p j < b
  /-- Assumption 4(b): `P(b) = Pr{D ≤ b} < 1` -/
  cdf_b_lt_one : ∑ j ∈ Finset.range (b + 1), p j < 1
  /-- `G(y)`, the one-period expected cost at inventory level `y` after ordering -/
  G : ℤ → ℝ
  /-- Assumption 1(b): `G` is nonnegative -/
  G_nonneg : ∀ y, 0 ≤ G y
  /-- Assumption 1(b): `G` is convex (second differences are nonnegative) -/
  G_convex : ∀ y, G y - G (y - 1) ≤ G (y + 1) - G y
  /-- Assumption 1(a): `G(y) → ∞` as `|y| → ∞` -/
  G_coercive : Tendsto G cofinite atTop
  /-- Assumption 3: the growth exponent `ρ`, a positive integer -/
  ρ : ℕ
  ρ_pos : 0 < ρ
  /-- Assumption 3: `G(y) ≤ A + B |y|^ρ` for positive constants `A`, `B` -/
  G_growth : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ y, G y ≤ A + B * |(y : ℝ)| ^ ρ

/-- Discrete convexity of `v` on the states `x ≤ U`. -/
def ConvexBelow (U : ℤ) (v : ℤ → ℝ) : Prop :=
  ∀ x : ℤ, x + 1 ≤ U → v x - v (x - 1) ≤ v (x + 1) - v x

/-- A one-period policy `δ` is feasible: `δ(x) ∈ Y(x) = {y : x ≤ y ≤ x + b, y ≤ U}` for every
state `x ≤ U` (values above `U` are irrelevant). -/
def Feasible (M : Model) (U : ℤ) (δ : ℤ → ℤ) : Prop :=
  ∀ x ≤ U, x ≤ δ x ∧ δ x ≤ x + M.b ∧ δ x ≤ U

/-- `δ ∈ Δ_L`: `δ` is feasible for the restricted action sets `Y_L(x)`, so it orders to capacity
(`δ(x) = x + b`) whenever `x ≤ L`. -/
def FeasibleL (M : Model) (U L : ℤ) (δ : ℤ → ℤ) : Prop :=
  Feasible M U δ ∧ ∀ x ≤ L, δ x = x + M.b

/-- The critical-number policy `δ[ȳ]` with critical number `ȳ`: order up to `ȳ` when possible,
otherwise order to capacity `b`; never order when `x ≥ ȳ`. -/
def critNum (M : Model) (ybar : ℤ) : ℤ → ℤ :=
  fun x => max x (min ybar (x + M.b))

/-- The transition operator `P[δ]w(x) = E w(δ(x) − D)` on nonnegative extended functions. -/
noncomputable def P (M : Model) (δ : ℤ → ℤ) (w : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (M.p j) * w (δ x - j)

/-- `periodCost M π i x = E{G(y_i) | x_0 = x, π}` for a Markov policy `π = (π 0, π 1, …)`, where
`y_t = π t (x_t)` and `x_{t+1} = y_t − D_t`. -/
noncomputable def periodCost (M : Model) : (ℕ → ℤ → ℤ) → ℕ → ℤ → ℝ≥0∞
  | π, 0, x => ENNReal.ofReal (M.G (π 0 x))
  | π, i + 1, x => P M (π 0) (periodCost M (fun t => π (t + 1)) i) x

/-- `totalCost M π t x = E{∑_{i=0}^{t-1} G(y_i) | x_0 = x, π}`. -/
noncomputable def totalCost (M : Model) (π : ℕ → ℤ → ℤ) (t : ℕ) (x : ℤ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, periodCost M π i x

/-- The stationary policy `δ` is strongly (average-cost) optimal with average cost `g`: it is
feasible, its average cost converges to `g` from every initial state `x ≤ U`, and every feasible
Markov policy has, from every initial state `x ≤ U`, a lim-inf average cost at least `g`. -/
def StronglyOptimal (M : Model) (U : ℤ) (δ : ℤ → ℤ) (g : ℝ) : Prop :=
  Feasible M U δ ∧
  (∀ x ≤ U, Tendsto (fun t : ℕ => totalCost M (fun _ => δ) t x / (t : ℝ≥0∞)) atTop
      (𝓝 (ENNReal.ofReal g))) ∧
  ∀ π : ℕ → ℤ → ℤ, (∀ t, Feasible M U (π t)) → ∀ x ≤ U,
    ENNReal.ofReal g ≤ liminf (fun t : ℕ => totalCost M π t x / (t : ℝ≥0∞)) atTop

/-- The operator `Rv(y) = G(y) + E v(y − D)`. -/
noncomputable def R (M : Model) (v : ℤ → ℝ) (y : ℤ) : ℝ :=
  M.G y + ∑' j : ℕ, M.p j * v (y - j)

/-- The value-iteration operator `Sv(x) = inf{Rv(y) : y ∈ Y(x)}`, meaningful for `x ≤ U`, where
`Y(x)` is finite and nonempty. -/
noncomputable def S (M : Model) (U : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨅ y : {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U}, R M v y

/-- The restricted value-iteration operator `S_L v(x) = inf{Rv(y) : y ∈ Y_L(x)}`. -/
noncomputable def SL (M : Model) (U L : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  if x ≤ L then R M v (x + M.b) else S M U v x

/-- The reduced operator `Qv(x) = Sv(x) − Sv(ȳ^∞)`. -/
noncomputable def Q (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  S M U v x - S M U v yInf

/-- The reduced restricted operator `Q_L v(x) = S_L v(x) − S_L v(ȳ^∞)`. -/
noncomputable def QL (M : Model) (U L yInf : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  SL M U L v x - SL M U L v yInf

/-- The optimality equation (6), `g + v(x) = min{Rv(y) : y ∈ Y(x)}` for every `x ≤ U`, stated
with explicit attainment of the minimum. -/
def OptEq (M : Model) (U : ℤ) (g : ℝ) (v : ℤ → ℝ) : Prop :=
  ∀ x ≤ U, (∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → g + v x ≤ R M v y) ∧
    ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧ g + v x = R M v y

/-- `δ ∈ Δ_ι` for `ι = [l, u]`: `δ` is feasible, orders to capacity for `x ≤ l`, and does not
order for `u ≤ x ≤ U`. -/
def DeltaIota (M : Model) (U l u : ℤ) (δ : ℤ → ℤ) : Prop :=
  Feasible M U δ ∧ (∀ x ≤ l, δ x = x + M.b) ∧ ∀ x, u ≤ x → x ≤ U → δ x = x

/-- The taboo transition operator of `δ`, which kills every path that enters `ι`. -/
noncomputable def tabooP (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (w : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (M.p j) * Set.indicator ιᶜ w (δ x - j)

/-- `hitSum M δ ι v x = E{∑_{t=0}^{T(ι)-1} v(y_t) | x_0 = x, δ}`, where `T(ι)` is the first
period `t ≥ 1` with `x_t ∈ ι`: the `t`-th term is `E{v(y_t); T(ι) > t}`. -/
noncomputable def hitSum (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (v : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' t : ℕ, (tabooP M δ ι)^[t] (fun z => v (δ z)) x

/-- `H_ι v(x) = sup_{δ ∈ Δ_ι} E{∑_{t=0}^{T(ι)-1} v(y_t) | x_0 = x, δ}` for `ι = [l, u]` and a
nonnegative function `v`. -/
noncomputable def H (M : Model) (U l u : ℤ) (v : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ⨆ δ : ℤ → ℤ, ⨆ (_ : DeltaIota M U l u δ), hitSum M δ (Set.Icc l u) v x

/-- The composite operator `P[σ 0] P[σ 1] ⋯ P[σ n]` of a finite sequence of one-period policies. -/
noncomputable def Pcomp (M : Model) : (ℕ → ℤ → ℤ) → ℕ → (ℤ → ℝ≥0∞) → ℤ → ℝ≥0∞
  | σ, 0, w => P M (σ 0) w
  | σ, n + 1, w => P M (σ 0) (Pcomp M (fun s => σ (s + 1)) n w)

/-- `v ∈ V`: `v ∈ V_{ρ+3}` (growth `O(|x|^{ρ+3})` on `x ≤ U`), `v` is nonincreasing below
`ȳ^∞` (`v(x+1) ≤ v(x)` for `x < ȳ^∞`), and `v` is convex on `x ≤ U`. -/
def InV (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) : Prop :=
  (∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) ∧
  (∀ x, x < yInf → v (x + 1) ≤ v x) ∧ ConvexBelow U v

end FedergruenZipkin.AvgCost
