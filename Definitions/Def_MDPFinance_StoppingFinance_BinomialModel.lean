import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.StoppingFinance

/-- The `[-∞,∞]`-valued integral `∫ v⁺ − ∫ v⁻` (with `∞ − ∞ = −∞`), used for expected rewards so
that no real integral silently returns `0`. -/
noncomputable def erealIntegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    EReal :=
  ((∫⁻ a, (v a ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal) + (-((∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal))

/-- The binomial model of Chapter 3 as §11.1 uses it (p. 331, 336): up/down factors `d < u`,
`d > 0`, discount `β = (1+i)^{-1} ∈ (0,1]`, risk-neutral probability `q ∈ (0,1)` with
`βqu + β(1−q)d = 1` (equivalently `d < 1+i < u`, (11.1)), strike `K > 0`, and a state space `E`
of positive prices closed under the moves. -/
structure BinomialModel where
  u : ℝ
  d : ℝ
  beta : ℝ
  q : ℝ
  K : ℝ
  E : Set ℝ
  d_lt_u : d < u
  d_pos : 0 < d
  beta_mem : beta ∈ Set.Ioc (0 : ℝ) 1
  q_mem : q ∈ Set.Ioo (0 : ℝ) 1
  K_pos : 0 < K
  E_pos : ∀ x ∈ E, 0 < x
  E_up : ∀ x ∈ E, x * u ∈ E
  E_down : ∀ x ∈ E, x * d ∈ E
  riskNeutral : beta * q * u + beta * (1 - q) * d = 1

/-- `(K − x)⁺`. -/
noncomputable def BinomialModel.payoff (M : BinomialModel) (x : ℝ) : ℝ := max (M.K - x) 0

/-- `𝒯P(x) = max{(K − x)⁺, β(qP(xu) + (1−q)P(xd))}` (p. 337). -/
noncomputable def BinomialModel.T (M : BinomialModel) (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (M.payoff x) (M.beta * (M.q * P (x * M.u) + (1 - M.q) * P (x * M.d)))

/-- `J_0(x) = (K − x)⁺`, `J_n(x) = max{(K − x)⁺, β(qJ_{n−1}(xu) + (1−q)J_{n−1}(xd))}` (p. 336). -/
noncomputable def BinomialModel.J (M : BinomialModel) : ℕ → ℝ → ℝ
  | 0 => M.payoff
  | (n + 1) => M.T (M.J n)

/-- `π_n(x) := J_{N−n}(x)`, the price of the American put at time `n` with maturity `N`. -/
noncomputable def BinomialModel.price (M : BinomialModel) (N n : ℕ) (x : ℝ) : ℝ :=
  M.J (N - n) x

/-- `J := lim_n J_n`, the limit of the increasing sequence `0 ≤ J_n ≤ K` (p. 337). -/
noncomputable def BinomialModel.Jlim (M : BinomialModel) (x : ℝ) : ℝ := ⨆ n, M.J n x

/-- `P` is **superharmonic**: `P(x) ≥ β(qP(xu) + (1−q)P(xd))` for `x ∈ E`. -/
def BinomialModel.Superharmonic (M : BinomialModel) (P : ℝ → ℝ) : Prop :=
  ∀ x ∈ M.E, M.beta * (M.q * P (x * M.u) + (1 - M.q) * P (x * M.d)) ≤ P x

open Classical in
/-- `𝒯_{f^*}` for the exercise rule `f^* = 1_{E^*}`: exercise on `E^*`, continue off it. -/
noncomputable def BinomialModel.Tf (M : BinomialModel) (Estar : Set ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y ∈ Estar then M.payoff y else M.beta * (M.q * g (y * M.u) + (1 - M.q) * g (y * M.d))

/-- `J_{f^*} := lim_n 𝒯_{f^*}^n 0` (p. 337), the limit of an increasing sequence bounded by `K`. -/
noncomputable def BinomialModel.JfStar (M : BinomialModel) (Estar : Set ℝ) (x : ℝ) : ℝ :=
  ⨆ n, ((M.Tf Estar)^[n] (fun _ => 0)) x

/-- The stock path: `S_0 = x`, each step multiplies by `u` or `d` according to `ω ∈ {up,down}^ℕ`. -/
noncomputable def BinomialModel.stock (M : BinomialModel) (x : ℝ) : ℕ → (ℕ → Bool) → ℝ
  | 0, _ => x
  | (n + 1), w => M.stock x n w * (if w n then M.u else M.d)

/-- The risk-neutral law `ℚ` of the moves: i.i.d. up moves with probability `q`, pinned by its
finite-dimensional distributions. -/
def BinomialModel.IsPathLaw (M : BinomialModel) (Q : Measure (ℕ → Bool)) : Prop :=
  IsProbabilityMeasure Q ∧
  ∀ (n : ℕ) (b : Fin n → Bool),
    Q {w : ℕ → Bool | ∀ i : Fin n, w (i : ℕ) = b i}
      = ∏ i : Fin n, (if b i then ENNReal.ofReal M.q else ENNReal.ofReal (1 - M.q))

/-- `τ` is a **stopping time** of the stock path: `{τ = n}` is decided by the first `n` moves
(a finite-coordinate event, hence measurable). Values in `ℕ∞`. -/
def IsStoppingTime (tau : (ℕ → Bool) → ℕ∞) : Prop :=
  ∀ (n : ℕ) (w w' : ℕ → Bool), (∀ i < n, w i = w' i) → (tau w = (n : ℕ∞) ↔ tau w' = (n : ℕ∞))

/-- `β^τ (K − S_τ)`, zero on `{τ = ∞}` (p. 337). -/
noncomputable def BinomialModel.reward (M : BinomialModel) (x : ℝ) (tau : (ℕ → Bool) → ℕ∞)
    (w : ℕ → Bool) : ℝ :=
  match tau w with
  | (n : ℕ) => M.beta ^ n * (M.K - M.stock x n w)
  | ⊤ => 0

/-- `β^τ (K − S_τ)⁺`, the finite-horizon exercise payoff (p. 332), zero on `{τ = ∞}`. -/
noncomputable def BinomialModel.rewardPlus (M : BinomialModel) (x : ℝ) (tau : (ℕ → Bool) → ℕ∞)
    (w : ℕ → Bool) : ℝ :=
  match tau w with
  | (n : ℕ) => M.beta ^ n * M.payoff (M.stock x n w)
  | ⊤ => 0

/-- `𝔼^ℚ_x[β^τ (K − S_τ)]` in `[-∞,∞]`. -/
noncomputable def BinomialModel.EReward (M : BinomialModel) (Q : Measure (ℕ → Bool)) (x : ℝ)
    (tau : (ℕ → Bool) → ℕ∞) : EReal :=
  erealIntegral Q (fun w => (M.reward x tau w : EReal))

noncomputable def BinomialModel.ERewardPlus (M : BinomialModel) (Q : Measure (ℕ → Bool)) (x : ℝ)
    (tau : (ℕ → Bool) → ℕ∞) : EReal :=
  erealIntegral Q (fun w => (M.rewardPlus x tau w : EReal))

/-- `P(x) := sup_{τ ≤ ∞} 𝔼^ℚ_x[β^τ (K − S_τ)]`, the price of the perpetual American put (p. 337). -/
noncomputable def BinomialModel.perpetualValue (M : BinomialModel) (Q : Measure (ℕ → Bool))
    (x : ℝ) : EReal :=
  ⨆ tau : (ℕ → Bool) → ℕ∞, ⨆ (_ : IsStoppingTime tau), M.EReward Q x tau

/-- `sup_{τ ≤ N} 𝔼^ℚ_x[β^τ (K − S_τ)⁺]`, the price of the American put with maturity `N`
(p. 332). -/
noncomputable def BinomialModel.finiteValue (M : BinomialModel) (Q : Measure (ℕ → Bool)) (N : ℕ)
    (x : ℝ) : EReal :=
  ⨆ tau : (ℕ → Bool) → ℕ∞, ⨆ (_ : IsStoppingTime tau ∧ ∀ w, tau w ≤ (N : ℕ∞)),
    M.ERewardPlus Q x tau

/-- `τ^* := inf{n ∈ ℕ₀ | S_n ∈ E^*}` (`inf ∅ = ∞`). -/
noncomputable def BinomialModel.exerciseTime (M : BinomialModel) (x : ℝ) (Estar : Set ℝ)
    (w : ℕ → Bool) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k w ∈ Estar})

/-- `τ^* := inf{n ∈ {0,…,N} | S_n ≤ x^*_n}` (Proposition 11.1.2 d)), capped at `N`. -/
noncomputable def BinomialModel.thresholdTime (M : BinomialModel) (x : ℝ) (xstar : ℕ → ℝ) (N : ℕ)
    (w : ℕ → Bool) : ℕ∞ :=
  min (sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k w ≤ xstar k})) (N : ℕ∞)

end MDPFinance.StoppingFinance
