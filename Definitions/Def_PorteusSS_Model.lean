import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-! The finite-horizon inventory model of §III with data `c` (ordering cost), `m` (holding and
shortage cost on ending inventory), `φ` (demand density), `f0` (terminal cost) and `α`
(discount factor). Periods are counted backwards: `n` is the number of periods remaining. -/

/-- `h_n` from its predecessor: given `f_{n-1}`, `h_n(y) = L(y) + α (f_{n-1} * φ)(y)` with
`L = m * φ`  (eq. (3)). -/
noncomputable def hStep (m φ : ℝ → ℝ) (α : ℝ) (fPrev : ℝ → ℝ) (y : ℝ) : ℝ :=
  conv m φ y + α * conv fPrev φ y

/-- The value functions of eqs. (2)/(4): `f_0 = f0` and
`f_n(x) = inf_{y ≥ x} {c(y - x) + h_n(y)}` for `n ≥ 1`. -/
noncomputable def valueFn (c m φ f0 : ℝ → ℝ) (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => f0
  | n + 1 => fun x => ⨅ y : Ici x, c ((y : ℝ) - x) + hStep m φ α (valueFn c m φ f0 α n) y

/-- `h_n = L + α f_{n-1} * φ` (eq. (3)), meaningful for `n ≥ 1`. -/
noncomputable def hFn (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  hStep m φ α (valueFn c m φ f0 α (n - 1)) y

/-- `Y_n(x)`, the set of optimal post-order inventory levels when the pre-order level is `x`
(p. 414): `S ≥ x` and `c(S - x) + h_n(S) ≤ c(y - x) + h_n(y)` for all `y ≥ x`. -/
def Yset (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) (x : ℝ) : Set ℝ :=
  {S | x ≤ S ∧ ∀ y : ℝ, x ≤ y →
    c (S - x) + hFn c m φ f0 α n S ≤ c (y - x) + hFn c m φ f0 α n y}

/-- `G_{κ n} = κ· + h_n` (eq. (7)), for a slope `κ ∈ C`. -/
noncomputable def Gfn (c m φ f0 : ℝ → ℝ) (α κ : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  κ * y + hFn c m φ f0 α n y

/-- The standing assumptions of §§II–III: the ordering cost satisfies §II, `0 ≤ α ≤ 1`,
the demand density `φ` is a one-sided Pólya density, and `m` is PF-integrable and bounded below. -/
structure IsModel (c m φ : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ) : Prop where
  cost : IsOrderingCost c c0 K0 cInf KInf
  alpha_nonneg : 0 ≤ α
  alpha_le_one : α ≤ 1
  density : IsOneSidedPolyaDensity φ
  m_pfIntegrable : PFIntegrable m
  m_bddBelow : BddBelow (range m)

/-- A1: `(c₀ - α c_∞)· + m` is nonincreasing on `R⁻ = (-∞, 0)`. -/
def AssumptionA1 (m : ℝ → ℝ) (α c0 cInf : ℝ) : Prop :=
  AntitoneOn (fun x => (c0 - α * cInf) * x + m x) (Iio 0)

/-- A2: `(c₀ - α c_∞) x + m(x) → ∞` as `x → -∞`. -/
def AssumptionA2 (m : ℝ → ℝ) (α c0 cInf : ℝ) : Prop :=
  Tendsto (fun x => (c0 - α * cInf) * x + m x) atBot atTop

/-- A3: `(1 - α) κ· + m` is non-`(1 - α) K_κ`-decreasing on `[0, ∞)` for `κ ∈ C`. -/
def AssumptionA3 (c m : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ κ ∈ slopeSet c,
    NonKDecreasingOn (fun x => (1 - α) * κ * x + m x) ((1 - α) * Kc c κ) (Ici 0)

/-- A4: `(1 - α) c_∞ x + m(x) → ∞` as `x → ∞`. -/
def AssumptionA4 (m : ℝ → ℝ) (α cInf : ℝ) : Prop :=
  Tendsto (fun x => (1 - α) * cInf * x + m x) atTop atTop

/-- A5: `f0` is piecewise continuous and PF-integrable, `c_∞· + f0` is nonincreasing on `R⁻`, and
`κ· + f0` is non-`K_κ`-decreasing on `ℝ` for `κ ∈ C`. -/
def AssumptionA5 (c f0 : ℝ → ℝ) (cInf : ℝ) : Prop :=
  PiecewiseContinuousOn f0 univ ∧ PFIntegrable f0 ∧
    AntitoneOn (fun x => cInf * x + f0 x) (Iio 0) ∧
    ∀ κ ∈ slopeSet c, NonKDecreasingOn (fun x => κ * x + f0 x) (Kc c κ) univ

end PorteusSS
