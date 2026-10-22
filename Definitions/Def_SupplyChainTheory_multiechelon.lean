import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-! ### Echelon accounting, Sect. 6.2.1 -/

/-- Table 6.1: the local holding cost `h'ⱼ = ∑_{i=j}^N hᵢ` recovered from echelon costs. -/
def localHolding (N : ℕ) (h : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.Icc j N, h i

/-- (6.4): the echelon holding cost `hⱼ = h'ⱼ − h'ⱼ₊₁`, with `h'_{N+1} = 0`. -/
def echelonHolding (N : ℕ) (h' : ℕ → ℝ) (j : ℕ) : ℝ :=
  h' j - (if j < N then h' (j + 1) else 0)

/-- (6.1): stage `j`'s echelon on-hand inventory `Iⱼ = ∑_{i=1}^j (I'ᵢ + ITᵢ₋₁)`, `IT₀ = 0`. -/
def echelonOnHand (I' IT : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 j, (I' i + if i = 1 then 0 else IT (i - 1))

/-! ### The Clark-Scarf recursion, Sect. 6.2.2 -/

/-- `ḡⱼ(x | S)` of (6.21)-(6.23), parametrised by the echelon base-stock vector `S`:
`ḡ₀(x) = (p + h'₁) x⁻` and `ḡⱼ₊₁(x) = gⱼ₊₁(min{Sⱼ₊₁, x})` with
`gⱼ₊₁(y) = E[hⱼ₊₁ (y − Dⱼ₊₁) + ḡⱼ(y − Dⱼ₊₁)]`. -/
noncomputable def csBar (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) :
    ℕ → ℝ → ℝ
  | 0 => fun x => (p + localHolding N h 1) * max (-x) 0
  | j + 1 => fun x =>
      ∫ d, (h (j + 1) * (min (S (j + 1)) x - d) + csBar N h p D S j (min (S (j + 1)) x - d))
        ∂(D (j + 1))

/-- (6.21): `ĝⱼ(x | S) = hⱼ x + ḡⱼ₋₁(x | S)`. -/
noncomputable def csHat (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (j : ℕ)
    (x : ℝ) : ℝ :=
  h j * x + csBar N h p D S (j - 1) x

/-- (6.22): `gⱼ(y | S) = E[ĝⱼ(y − Dⱼ | S)]`; the system cost of `S` is `g_N(S_N | S)`. -/
noncomputable def csG (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (j : ℕ)
    (y : ℝ) : ℝ :=
  ∫ d, csHat N h p D S j (y - d) ∂(D j)

/-- (6.26): `S` is sequentially optimal when each `Sⱼ` minimises `gⱼ(· | S)`, which depends
only on `S₁, …, Sⱼ₋₁`. -/
def CSSequential (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 N, ∀ y, csG N h p D S j (S j) ≤ csG N h p D S j y

/-! ### The Shang-Song bounds, Sect. 6.2.3 -/

/-- The lead-time demand `D̃ⱼ = D₁ + ⋯ + Dⱼ` of the single-stage system with lead time
`L₁ + ⋯ + Lⱼ`, as the convolution of the stage laws. -/
noncomputable def tildeLaw (D : ℕ → Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | j + 1 => (tildeLaw D j).conv (D (j + 1))

/-- The single-stage newsvendor cost with holding cost `a`, stockout cost `b`, demand law `μ`. -/
noncomputable def nvCostOf (a b : ℝ) (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ d, (a * max (y - d) 0 + b * max (d - y) 0) ∂μ

/-- The expected pipeline stock of the `j`-stage truncated system, `E[D₁] + ⋯ + E[Dⱼ₋₁]`: the
stock in transit to stages `1, …, j − 1`, on which (6.31) charges holding cost. -/
noncomputable def pipelineMean (D : ℕ → Measure ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 j, ∫ d, d ∂(D i)

/-- `gˡⱼ`: (6.31) with every local holding cost replaced by `hⱼ`, when all stock is held at
stage 1: the single-stage newsvendor cost for `D̃ⱼ` plus the pipeline holding cost. -/
noncomputable def ssLower (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (j : ℕ) (y : ℝ) :
    ℝ :=
  nvCostOf (h j) (p + localHolding N h (j + 1)) (tildeLaw D j) y + h j * pipelineMean D j

/-- `gᵘⱼ`: (6.31) with every local holding cost replaced by `∑_{k=1}^j hₖ`. -/
noncomputable def ssUpper (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (j : ℕ) (y : ℝ) :
    ℝ :=
  nvCostOf (∑ k ∈ Finset.Icc 1 j, h k) (p + localHolding N h (j + 1)) (tildeLaw D j) y
    + (∑ k ∈ Finset.Icc 1 j, h k) * pipelineMean D j

/-! ### Guaranteed-service serial systems, Sect. 6.3.4 -/

/-- The inbound committed service time `SIᵢ`: `Sᵢ₊₁` for `i < N`, the external `SI_N` at `N`. -/
def gsInbound (N : ℕ) (SIN : ℝ) (S : ℕ → ℝ) (i : ℕ) : ℝ := if i < N then S (i + 1) else SIN

/-- (6.37): the expected holding cost `g(S) = ∑ᵢ hᵢ k √(SIᵢ + Tᵢ − Sᵢ)` with `k = z_α σ`. -/
noncomputable def gsCost (N : ℕ) (h : ℕ → ℝ) (k : ℝ) (T : ℕ → ℝ) (SIN : ℝ) (S : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, h i * k * Real.sqrt (gsInbound N SIN S i + T i - S i)

/-- (6.39)-(6.42) without integrality: every CST and every net lead time is nonnegative. -/
def GSFeasible (N : ℕ) (T : ℕ → ℝ) (SIN : ℝ) (S : ℕ → ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 N, 0 ≤ S i) ∧ (∀ i ∈ Finset.Icc 1 N, S i ≤ gsInbound N SIN S i + T i)

end SupplyChainTheory
