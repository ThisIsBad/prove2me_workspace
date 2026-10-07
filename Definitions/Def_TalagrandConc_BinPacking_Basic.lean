import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.BinPacking

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 151: an assignment of the items `x₁, …, x_N` (sizes in `[0, 1]`) to
`k` unit bins such that the sum of the sizes of the items attributed to each bin is at most one. -/
def IsPacking {N : ℕ} (x : Fin N → unitInterval) (k : ℕ) : Prop :=
  ∃ σ : Fin N → Fin k, ∀ j : Fin k,
    ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (x i : ℝ) ≤ 1

/-- Talagrand (1995), p. 151: `B_N(x₁, …, x_N)`, the **minimum** number of unit bins in which the
items can be packed. The set of admissible `k` is nonempty (`k = N`, one item per bin), so the
`sInf` in `ℕ` is attained; for `N = 0` it is `0`. -/
noncomputable def binNumber {N : ℕ} (x : Fin N → unitInterval) : ℕ :=
  sInf {k : ℕ | IsPacking x k}

/-- Talagrand (1995), p. 151: `‖x‖₂ = (∑_{i ≤ N} x_i²)^{1/2}` (Euclidean norm). -/
noncomputable def l2Norm {N : ℕ} (x : Fin N → unitInterval) : ℝ :=
  Real.sqrt (∑ i, (x i : ℝ) ^ 2)

/-- Talagrand (1995), p. 151: `A(a) = {y ∈ Ω^N ; B_N(y) ≤ a}` (the paper uses it for `a > 0`). -/
def levelSet (N : ℕ) (a : ℝ) : Set (Fin N → unitInterval) :=
  {y | (binNumber y : ℝ) ≤ a}

/-- Talagrand (1995), p. 123: `f_c(A, x)`, the `ℓ²`-distance from zero to `V_A(x)`,
`inf { (∑_i s_i²)^{1/2} ; s ∈ V_A(x) }`, valued in `ℝ≥0∞` (it is `⊤ = +∞` when `A = ∅`).
This is the shared definition `TalagrandConc.ConvexHull.fc` of Section 4.1, under the name used
in Chapter 6. -/
noncomputable def convexDist {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) :
    ℝ≥0∞ :=
  TalagrandConc.ConvexHull.fc A x

/-- `E X₁² = ∫ ω² dμ(ω)` for the common law `μ` of the items on `Ω = [0, 1]`. -/
noncomputable def secondMoment (μ : Measure unitInterval) : ℝ :=
  ∫ ω, (ω : ℝ) ^ 2 ∂μ

/-- `M` is a median of the real function `Z` under `P`:
`P(Z ≤ M) ≥ 1/2` and `P(Z ≥ M) ≥ 1/2`. -/
def IsMedian {α : Type*} [MeasurableSpace α] (P : Measure α) (Z : α → ℝ) (M : ℝ) : Prop :=
  (1 / 2 : ℝ≥0∞) ≤ P {x | Z x ≤ M} ∧ (1 / 2 : ℝ≥0∞) ≤ P {x | M ≤ Z x}

end TalagrandConc.BinPacking
