import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.OptimalStopping

/-! ## The house selling problem (§10.3.1, p. 316) -/

/-- The **house selling problem** (p. 316): i.i.d. offers with law `Q` on `[m,M]`, `0 < m < M`,
maintenance cost `c > 0` per rejection; `E := [m,M]`, `Q^X(·|x) := Q`, `c(x) ≡ -c`, `g(x) := x`;
for the unbounded horizon `β ∈ (0,1)` (p. 317). -/
structure HouseSelling where
  m : ℝ
  M : ℝ
  Q : Measure ℝ
  c : ℝ
  beta : ℝ
  m_pos : 0 < m
  m_lt_M : m < M
  Q_prob : IsProbabilityMeasure Q
  Q_supp : Q {x : ℝ | x < m ∨ M < x} = 0
  c_pos : 0 < c
  beta_mem : beta ∈ Set.Ioo (0 : ℝ) 1

def HouseSelling.E (H : HouseSelling) : Set ℝ := Set.Icc H.m H.M

/-- `x ↦ (-c Q([m,x)) + ∫_x^∞ x' Q(dx')) / (1 − β Q([m,x)))` (Theorem 10.3.1). -/
noncomputable def HouseSelling.thresholdObjective (H : HouseSelling) (x : ℝ) : ℝ :=
  (-H.c * (H.Q (Set.Ico H.m x)).toReal + ∫ y in Set.Ici x, y ∂H.Q)
    / (1 - H.beta * (H.Q (Set.Ico H.m x)).toReal)

noncomputable def HouseSelling.toProblem (H : HouseSelling) : StationaryProblem ℝ where
  QX := fun _ => H.Q
  QX_prob := fun _ => H.Q_prob
  QX_meas := measurable_const
  c := fun _ => -H.c
  c_meas := measurable_const
  g := fun x => x
  g_meas := measurable_id
  beta := H.beta
  beta_mem := ⟨H.beta_mem.1, le_of_lt H.beta_mem.2⟩

/-! ## The secretary problem (§10.3.2, pp. 319-322) -/

/-- The **secretary problem** (p. 321) with `N > 2` candidates. -/
structure Secretary where
  N : ℕ
  N_ge : 3 ≤ N

/-- The transition probabilities **(10.4)**. -/
noncomputable def Secretary.q (S : Secretary) (x y : ℕ) : ℝ :=
  if x = S.N + 1 then (if y = S.N + 1 then 1 else 0)
  else if y = S.N + 1 then (x : ℝ) / (S.N : ℝ)
  else if x < y ∧ y ≤ S.N then (x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))
  else 0

/-- `g(N+1) = 0`, `g(x) = x/N` for `x = 1,…,N`. -/
noncomputable def Secretary.g (S : Secretary) (x : ℕ) : ℝ :=
  if x = S.N + 1 then 0 else (x : ℝ) / (S.N : ℝ)

/-- The value functions by periods still to run: `W 0 = V_{N-1}`, `W (j+1) (x) = max{x/N,
Σ_{y=x+1}^N (x/(y(y-1))) W j (y)}` (p. 321). -/
noncomputable def Secretary.W (S : Secretary) : ℕ → ℕ → ℝ
  | 0, x => (x : ℝ) / (S.N : ℝ)
  | (j + 1), x =>
      max ((x : ℝ) / (S.N : ℝ))
        (∑ y ∈ Finset.Icc (x + 1) S.N, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y)

/-- `V_n = W_{N-1-n}` for `n = 0,…,N-1`. -/
noncomputable def Secretary.V (S : Secretary) (n x : ℕ) : ℝ := S.W (S.N - 1 - n) x

/-- `h(x) := 1/x + … + 1/(N-1)` (p. 322), as a function of the horizon. -/
noncomputable def secretaryH (N x : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico x N, (1 : ℝ) / (j : ℝ)

/-- `k^*(N) := inf{k ∈ {1,…,N-2} | h(k) > 1 ≥ h(k+1)}` **(10.5)**. -/
noncomputable def secretaryKStar (N : ℕ) : ℕ :=
  sInf {k : ℕ | k ∈ Finset.Icc 1 (N - 2) ∧ 1 < secretaryH N k ∧ secretaryH N (k + 1) ≤ 1}

noncomputable def Secretary.h (S : Secretary) (x : ℕ) : ℝ := secretaryH S.N x

noncomputable def Secretary.kStar (S : Secretary) : ℕ := secretaryKStar S.N

/-! ### The general Bayesian stopping problem (§10.3.4, pp. 323-324) -/

/-- `μ ≤_lr ν`, the likelihood ratio order (Definition B.3.5): densities `f`, `g` against a
common reference measure with `f(θ')g(θ) ≤ f(θ)g(θ')` for `θ ≤ θ'`. -/
def LikelihoodRatioLe (mu nu : Measure ℝ) : Prop :=
  ∃ (lam : Measure ℝ) (f g : ℝ → ℝ),
    (∀ θ, 0 ≤ f θ) ∧ (∀ θ, 0 ≤ g θ) ∧ Measurable f ∧ Measurable g ∧
    mu = lam.withDensity (fun θ => ENNReal.ofReal (f θ)) ∧
    nu = lam.withDensity (fun θ => ENNReal.ofReal (g θ)) ∧
    ∀ θ θ' : ℝ, θ ≤ θ' → f θ' * g θ ≤ f θ * g θ'

/-- `q(z|θ)` is **`MTP_2`** in `z` and `θ`. -/
def IsMTP2 (q : ℝ → ℝ → ℝ) : Prop :=
  ∀ z z' θ θ' : ℝ, q z θ * q z' θ' ≤ q (max z z') (max θ θ') * q (min z z') (min θ θ')

/-- The **general Bayesian stopping problem** of §10.3.4 (pp. 323-324): i.i.d. offers with law
`Q(·|θ)` of Lebesgue density `q(·|θ)`, unknown `θ`; information `i ∈ I` with posterior
`μ̂(·|i)` and update `Φ̂(i,z)` — the *Bayes* update, `μ̂(·|Φ̂(i,z)) ∝ q(z|·) μ̂(·|i)` (§5.4);
`sup_θ ∫ z Q(dz|θ) < ∞` (for (B_N)); cost `c ≥ 0` of continuing; stopping reward the offer;
`β = 1`. -/
structure GenBayesStopping (I : Type*) [MeasurableSpace I] where
  q : ℝ → ℝ → ℝ
  q_nonneg : ∀ z θ, 0 ≤ q z θ
  q_meas : Measurable fun p : ℝ × ℝ => q p.1 p.2
  q_density : ∀ θ, ∫⁻ z, ENNReal.ofReal (q z θ) = 1
  hmom : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ θ, ∫⁻ z, ENNReal.ofReal z * ENNReal.ofReal (q z θ) ≤ K
  muhat : I → Measure ℝ
  muhat_prob : ∀ i, IsProbabilityMeasure (muhat i)
  Phi : I → ℝ → I
  /-- The Bayes update: wherever the predictive density is positive,
  `μ̂(·|Φ̂(i,z)) = q(z|·) μ̂(·|i) / ∫ q(z|θ) μ̂(dθ|i)`. -/
  hbayes : ∀ i z, 0 < ∫⁻ θ, ENNReal.ofReal (q z θ) ∂(muhat i) →
    muhat (Phi i z) = (∫⁻ θ, ENNReal.ofReal (q z θ) ∂(muhat i))⁻¹ •
      (muhat i).withDensity (fun θ => ENNReal.ofReal (q z θ))
  cost : ℝ
  cost_nonneg : 0 ≤ cost

variable {I : Type*} [MeasurableSpace I]

/-- `J_0(x,i) = x`, `J_n(x,i) = max{x, −c + ∫∫ J_{n-1}(z, Φ̂(i,z)) Q(dz|θ) μ̂(dθ|i)}` (p. 324), in
`[-∞,∞]` (the double integral is a genuine value in `[-∞,∞)` under the moment condition). -/
noncomputable def GenBayesStopping.J (M : GenBayesStopping I) : ℕ → ℝ → I → EReal
  | 0, x, _ => (x : EReal)
  | (k + 1), x, i =>
      max (x : EReal) (-(M.cost : EReal) + erealIntegral (M.muhat i)
        (fun θ => erealIntegral volume (fun z => M.J k z (M.Phi i z) * (M.q z θ : EReal))))

/-- `c_n(i) := −c + ∫∫ J_{n-1}(z, Φ̂(i,z)) Q(dz|θ) μ̂(dθ|i)`, `n ≥ 1`. -/
noncomputable def GenBayesStopping.cfun (M : GenBayesStopping I) (n : ℕ) (i : I) : EReal :=
  -(M.cost : EReal) + erealIntegral (M.muhat i)
    (fun θ => erealIntegral volume (fun z => M.J (n - 1) z (M.Phi i z) * (M.q z θ : EReal)))

/-- `i ≤ i' :⟺ μ̂(·|i) ≤_lr μ̂(·|i')` (p. 324). -/
def GenBayesStopping.Ile (M : GenBayesStopping I) (i i' : I) : Prop :=
  LikelihoodRatioLe (M.muhat i) (M.muhat i')

/-- `(x,i) ≤ (x',i') :⟺ x ≤ x'` and `i ≤ i'`. -/
def GenBayesStopping.Ele (M : GenBayesStopping I) (p p' : ℝ × I) : Prop :=
  p.1 ≤ p'.1 ∧ M.Ile p.2 p'.2

/-! ## The Bayesian stopping problem with exponential offers and Inverse Gamma prior
(Example 10.3.5, pp. 325-326) -/

/-- Example 10.3.5: `c = 0`, exponential offers with unknown mean `θ`, sufficient statistic
`i = (s,n)`, Inverse Gamma prior with `a > 1`, `b > 0`; posterior predictive
`Q̂^Z(·|s,n) = Be(1, a+n, s+b)`, density `(n+a)(s+b)^{n+a}/(z+s+b)^{n+a+1}` on `z > 0`. -/
structure BayesStopping where
  a : ℝ
  b : ℝ
  a_gt : 1 < a
  b_pos : 0 < b

noncomputable def BayesStopping.qZ (M : BayesStopping) (s : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ((n : ℝ) + M.a) * (s + M.b) ^ ((n : ℝ) + M.a) / (z + s + M.b) ^ ((n : ℝ) + M.a + 1)

/-- `J_0(x,i) = x`, `J_k(x,(s,n)) = max{x, ∫ J_{k-1}(z,(s+z,n+1)) Q̂^Z(dz|s,n)}` (`c = 0`). -/
noncomputable def BayesStopping.J (M : BayesStopping) : ℕ → ℝ → ℝ → ℕ → ℝ
  | 0, x, _, _ => x
  | (k + 1), x, s, n =>
      max x (∫ z in Set.Ioi (0 : ℝ), M.J k z (s + z) (n + 1) * M.qZ s n z)

/-- `c_k((s,n)) := ∫ J_{k-1}(z,(s+z,n+1)) Q̂^Z(dz|s,n)`, `k ≥ 1`. -/
noncomputable def BayesStopping.cfun (M : BayesStopping) (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), M.J (k - 1) z (s + z) (n + 1) * M.qZ s n z

/-- `ĉ_1 = 1/(N+a-2)` and, with `k := N - j`, `ĉ_{j+1} = (1/(k+a-2))[(k+a-1)ĉ_j +
((1-ĉ_j)^+)^{k+a-1}]` (Theorem 10.3.6 a)); `ĉ_0` unused. -/
noncomputable def BayesStopping.chat (M : BayesStopping) (N : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / ((N : ℝ) + M.a - 2)
  | (j + 2) =>
      let k : ℝ := (N : ℝ) - ((j : ℝ) + 1)
      (1 / (k + M.a - 2)) *
        ((k + M.a - 1) * M.chat N (j + 1)
          + Real.rpow (max (1 - M.chat N (j + 1)) 0) (k + M.a - 1))

/-- `n^*(N) := max{k ∈ {1,…,N} | ĉ_{N-k+1} ≥ 1}`, `max ∅ := 0`. -/
noncomputable def BayesStopping.nStar (M : BayesStopping) (N : ℕ) : ℕ :=
  sSup {k : ℕ | k ∈ Finset.Icc 1 N ∧ 1 ≤ M.chat N (N - k + 1)}

end MDPFinance.OptimalStopping
