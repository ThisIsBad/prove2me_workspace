import Mathlib
import Definitions.Def_ZhengQR_Flatness_costRates
import Definitions.Def_ZhengQR_Flatness_QRMachinery

namespace ZhengQR.Flatness

/-- The standing assumptions of Zheng (1992), pp. 88–90 and 94: demand rate `lam`, positive
fixed leadtime `L`, fixed ordering cost `K`, holding and backorder cost rates `h`, `p`, all
positive; a nonnegative, integrable leadtime demand `D ∼ μ` with `E(D) = λL`; and the
assumption that `G` achieves its minimum at a unique point `y⁰`. -/
structure QRModel where
  lam : ℝ
  L : ℝ
  K : ℝ
  h : ℝ
  p : ℝ
  μ : MeasureTheory.Measure ℝ
  isProb : MeasureTheory.IsProbabilityMeasure μ
  lam_pos : 0 < lam
  L_pos : 0 < L
  K_pos : 0 < K
  h_pos : 0 < h
  p_pos : 0 < p
  integrable : MeasureTheory.Integrable (fun x : ℝ => x) μ
  mean_eq : ∫ x, x ∂μ = lam * L
  demand_nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  unique_min : ∃! y : ℝ, ∀ z : ℝ, newsvendorCost h p μ y ≤ newsvendorCost h p μ z

namespace QRModel

variable (M : QRModel)

/-- The stochastic inventory cost rate `G` (p. 88). -/
noncomputable def G : ℝ → ℝ := newsvendorCost M.h M.p M.μ
/-- The EOQ inventory cost rate `G_d` (p. 94). -/
noncomputable def Gd : ℝ → ℝ := eoqCost M.h M.p M.lam M.L
/-- `c(Q, r)`, Eq. (1). -/
noncomputable def c (Q r : ℝ) : ℝ := qrCost M.G M.lam M.K Q r
/-- `r(Q)`, the optimal reorder point for `Q` fixed (p. 90). -/
noncomputable def r (Q : ℝ) : ℝ := optReorder M.G M.lam M.K Q
/-- `y⁰`, the minimizer of `G` (p. 90). -/
noncomputable def y0 : ℝ := minPoint M.G
/-- `H(Q)`, Eq. (6). -/
noncomputable def H (Q : ℝ) : ℝ := Hfun M.G M.lam M.K Q
/-- `H₀(Q) = H(Q) - G(y⁰)` (p. 92). -/
noncomputable def H0 (Q : ℝ) : ℝ := Hzero M.G M.lam M.K Q
/-- `C(Q) = c(Q, r(Q))` (p. 91). -/
noncomputable def C (Q : ℝ) : ℝ := optCost M.G M.lam M.K Q
/-- `A(Q)`, Eq. (9). -/
noncomputable def A (Q : ℝ) : ℝ := Afun M.G M.lam M.K Q
/-- `r_d(Q)`: the optimal reorder point of the EOQ model for `Q` fixed, i.e. `r(Q)` at `G_d`
(p. 94). -/
noncomputable def rd (Q : ℝ) : ℝ := optReorder M.Gd M.lam M.K Q
/-- `H_d(Q)`: `H` of the EOQ model, i.e. Eq. (6) at `G_d` (p. 94). -/
noncomputable def Hd (Q : ℝ) : ℝ := Hfun M.Gd M.lam M.K Q
/-- `A_d(Q)`: `A` of the EOQ model, i.e. Eq. (9) at `G_d` (p. 94). -/
noncomputable def Ad (Q : ℝ) : ℝ := Afun M.Gd M.lam M.K Q

/-- `Q` is an optimal order quantity: `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0` (p. 92). -/
def IsOptQty (Q : ℝ) : Prop := 0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → M.C Q ≤ M.C Q'

end QRModel

end ZhengQR.Flatness
