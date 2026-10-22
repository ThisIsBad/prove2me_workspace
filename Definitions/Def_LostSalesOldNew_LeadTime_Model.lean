import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

/-- The cost data of §2 (p. 1257): unit procurement cost `c`, unit holding cost `ĥ` (`hhat`), unit
lost-sales penalty `p`, discount factor `γ < 1`. The signs are implicit in the paper (they are
costs); `γ < 1` is the paper's condition for (3). -/
structure Costs where
  c : ℝ
  hhat : ℝ
  p : ℝ
  γ : ℝ
  c_nonneg : 0 ≤ c
  hhat_nonneg : 0 ≤ hhat
  p_nonneg : 0 ≤ p
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

/-- The transformed holding cost `h = ĥ − γc` (p. 1257). It may be negative. -/
def Costs.h (K : Costs) : ℝ := K.hhat - K.γ * K.c

/-- `q^0(y) = c y + h E[[y − d]^+] + p E[[y − d]^−]` (p. 1257), with `[a]^− = max(−a, 0)`, the
demand `d` distributed according to `D`. -/
noncomputable def q0 (K : Costs) (D : Measure ℝ) (y : ℝ) : ℝ :=
  K.c * y + K.h * ∫ d, max (y - d) 0 ∂D + K.p * ∫ d, max (d - y) 0 ∂D

/-- `y_{+l}`: the stock on hand `l` periods later, after that period's arrival, computed from the
subvector `x^l = (x_0, …, x_l)` and the demands `ds 0, …, ds (l−1)` of the `l` periods in between
(`ds 0` is the current period's demand). -/
noncomputable def yAfter : (l : ℕ) → (Fin (l + 1) → ℝ) → (Fin l → ℝ) → ℝ
  | 0, x, _ => x 0
  | l + 1, x, ds => yAfter l (LostSalesOldNew.StateReduction.shift x (ds 0)) (Fin.tail ds)

/-- `q^l(x^l) = γ^l E[q^0(y_{+l})]` (p. 1257), the demands of the `l` intervening periods i.i.d.
with law `D` (the product measure `D^{⊗l}`). -/
noncomputable def qL (K : Costs) (D : Measure ℝ) (l : ℕ) (x : Fin (l + 1) → ℝ) : ℝ :=
  K.γ ^ l * ∫ ds, q0 K D (yAfter l x ds) ∂(Measure.pi fun _ : Fin l => D)

/-- The dynamic-programming operator of (2)–(3) for the system with lead time `L`:
`(T f)(x) = inf_{z ≥ 0} { q(x, z) + γ E[f(x_+)] }`, with `q(x, z) = q^L(x^L)`, `x^L = (x, z)`.
Values in `[0, ∞]`. -/
noncomputable def bellman (K : Costs) (D : Measure ℝ) (L : ℕ) (f : (Fin L → ℝ) → ENNReal)
    (x : Fin L → ℝ) : ENNReal :=
  ⨅ (z : ℝ) (_ : 0 ≤ z),
    (ENNReal.ofReal (qL K D L (Fin.snoc (α := fun _ => ℝ) x z))
      + ENNReal.ofReal K.γ * ∫⁻ d, f (LostSalesOldNew.StateReduction.next x z d) ∂D)

/-- (2): the optimal cost with `n` periods to go, `f_{T+1−n}`, obtained from `f_{T+1} = 0` by `n`
applications of the operator. -/
noncomputable def fH (K : Costs) (D : Measure ℝ) (L : ℕ) : ℕ → (Fin L → ℝ) → ENNReal
  | 0 => fun _ => 0
  | n + 1 => bellman K D L (fH K D L n)

/-- `f*^L`: the infinite-horizon optimal discounted cost of the system with lead time `L`, the
limit (supremum) of the finite-horizon optimal costs (2) as the horizon grows. -/
noncomputable def fStar (K : Costs) (D : Measure ℝ) (L : ℕ) (x : Fin L → ℝ) : ENNReal :=
  ⨆ n, fH K D L n x

end LostSalesOldNew.LeadTime
