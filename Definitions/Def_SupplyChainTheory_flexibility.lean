import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-! ### Risk pooling, Sect. 7.2 -/

/-- Sect. 7.2.4: the pooled variance `σ₀² = ∑ᵢ ∑ⱼ σᵢⱼ` with `σᵢⱼ = σᵢ σⱼ ρᵢⱼ`. -/
def pooledVariance {N : ℕ} (sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, sig i * sig j * rho i j

/-- The optimal single-location newsvendor cost `min_S g(S)` for a demand law `D`
(Sect. 7.2.3), as an infimum over all base-stock levels. -/
noncomputable def optNvCost (h p : ℝ) (D : Measure ℝ) : ℝ :=
  sInf (Set.range (fun S : ℝ => ∫ d, (h * max (S - d) 0 + p * max (d - S) 0) ∂D))

/-! ### Transshipments, Sect. 7.4 -/

/-- Complete pooling (Sect. 7.4.2): the amount `Y_{ji}` transshipped from retailer `j` to
retailer `i` when the base-stock levels are `Sj, Si` and the demands `dj, di`:
`min{Sj − Dj, Di − Si}` if `j` has a surplus and `i` a shortage, `0` otherwise. -/
noncomputable def transship (Sj Si dj di : ℝ) : ℝ :=
  if dj < Sj ∧ Si < di then min (Sj - dj) (di - Si) else 0

/-- `E[Y_{ji}]`, the expected transshipment quantity from `j` to `i`, the demands being
independent with laws `Dj`, `Di`. -/
noncomputable def expTransship (Sj Si : ℝ) (Dj Di : Measure ℝ) : ℝ :=
  ∫ q, transship Sj Si q.1 q.2 ∂(Dj.prod Di)

/-- `α⁰ᵢ(S)`: the type-1 service level at retailer `i` without transshipments, `P(Dᵢ ≤ Sᵢ)`. -/
noncomputable def type1NoTrans (Si : ℝ) (Di : Measure ℝ) : ℝ := Di.real (Set.Iic Si)

/-- `αᵢ(S)`: the type-1 service level at retailer `i` with transshipments, the probability that
the shortage `Dᵢ − Sᵢ` is covered by the transshipment from `j`. -/
noncomputable def type1Trans (Sj Si : ℝ) (Dj Di : Measure ℝ) : ℝ :=
  (Dj.prod Di).real {q | q.2 - Si ≤ transship Sj Si q.1 q.2}

/-- `β⁰ᵢ(S)`: the type-2 service level (fill rate) at `i` without transshipments,
`1 − E[(Dᵢ − Sᵢ)⁺] / E[Dᵢ]`. -/
noncomputable def type2NoTrans (Si : ℝ) (Di : Measure ℝ) : ℝ :=
  1 - (∫ d, max (d - Si) 0 ∂Di) / (∫ d, d ∂Di)

/-- `βᵢ(S)`: the type-2 service level at `i` with transshipments,
`1 − E[(Dᵢ − Sᵢ − Y_{ji})⁺] / E[Dᵢ]`. -/
noncomputable def type2Trans (Sj Si : ℝ) (Dj Di : Measure ℝ) : ℝ :=
  1 - (∫ q, max (q.2 - Si - transship Sj Si q.1 q.2) 0 ∂(Dj.prod Di)) / (∫ d, d ∂Di)

/-! ### Process flexibility, Sect. 7.5 -/

/-- A production plan `y` is feasible for capacity `C`, demand `d` and design `E`
((7.23)-(7.26)): nonnegative, zero off `E`, plant capacities and product demands respected. -/
def FlexFeasible {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι))
    (y : ι → ι → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧ (∀ i j, (i, j) ∉ E → y i j = 0) ∧ (∀ j, ∑ i, y i j ≤ C)
    ∧ (∀ i, ∑ j, y i j ≤ d i)

/-- `P(d, E)`, (7.22): the maximum sales for the demand realization `d` under design `E`. -/
noncomputable def perf {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι)) : ℝ :=
  sSup {v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j}

/-- A balanced system of size `n` with exchangeable demand (Sect. 7.5.3): `n` products, `n`
plants of common capacity `C`, and a nonnegative integrable demand vector `D` whose joint law
is invariant under every permutation of the products. -/
structure BalancedSystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  D : Fin n → Ω → ℝ
  measurable_D : ∀ i, Measurable (D i)
  integrable_D : ∀ i, Integrable (D i) P
  D_nonneg : ∀ i ω, 0 ≤ D i ω
  exchangeable : ∀ σ : Equiv.Perm (Fin n),
    P.map (fun ω i => D (σ i) ω) = P.map (fun ω i => D i ω)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `[E] = E[P(D, E)]`, the expected performance of a design. -/
noncomputable def BalancedSystem.expPerf {n : ℕ} (S : BalancedSystem P n)
    (E : Finset (Fin n × Fin n)) : ℝ :=
  ∫ ω, perf S.C (fun i => S.D i ω) E ∂P

/-- The demand of the subsystem formed by products and plants `1, …, k`. -/
noncomputable def BalancedSystem.subDemand {n : ℕ} (S : BalancedSystem P n) (k : ℕ) (ω : Ω)
    (i : Fin k) : ℝ :=
  if h : i.val < n then S.D ⟨i.val, h⟩ ω else 0

/-- `[E]` for a design `E` of the subsystem of size `k`. -/
noncomputable def BalancedSystem.subPerf {n : ℕ} (S : BalancedSystem P n) (k : ℕ)
    (E : Finset (Fin k × Fin k)) : ℝ :=
  ∫ ω, perf S.C (S.subDemand k ω) E ∂P

/-- The dedicated design `Dₙ = {(i, i)}`. Edges are (product, plant) pairs. -/
def dedicated (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.image (fun i => (i, i))

/-- The long-chain design `Cₙ = Dₙ ∪ {(i + 1, i)} ∪ {(1, n)}`: plant `i` makes products `i`
and `i + 1`, indices mod `n`. -/
def longChain (n : ℕ) : Finset (Fin n × Fin n) :=
  dedicated n ∪ Finset.univ.image (fun i => (finRotate n i, i))

/-- The open chain `Lₖ`, the long chain `Cₖ` with the edge `(1, k)` removed. -/
def openChain (k : ℕ) : Finset (Fin k × Fin k) :=
  dedicated k ∪ (Finset.univ.filter (fun i : Fin k => i.val + 1 < k)).image
    (fun i => (finRotate k i, i))

/-- `Lⁿₖ`: the open chain through products and plants `1, …, k` together with the dedicated
edges `(i, i)`, `i = k + 1, …, n`; `Lⁿ₁ = Dₙ` and `Lⁿₙ = Lₙ`. -/
def partialChain (n k : ℕ) : Finset (Fin n × Fin n) :=
  dedicated n ∪ (Finset.univ.filter (fun i : Fin n => i.val + 1 < k)).image
    (fun i => (finRotate n i, i))

/-- A flexible edge is one that is not dedicated. -/
def IsFlexEdge {n : ℕ} (e : Fin n × Fin n) : Prop := e.1 ≠ e.2

/-- A 2-flexibility design: every product is made at exactly two plants and every plant makes
exactly two products. -/
def TwoFlex {n : ℕ} (A : Finset (Fin n × Fin n)) : Prop :=
  (∀ i, (A.filter (fun e => e.1 = i)).card = 2)
    ∧ (∀ j, (A.filter (fun e => e.2 = j)).card = 2)

end SupplyChainTheory
