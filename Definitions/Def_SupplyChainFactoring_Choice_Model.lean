import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- The exogenous data of the model (Kouvelis–Xu 2021, §3–§5): unit production cost `c`, retail
price `p`, lead time `t1`, payment term `t2`, the supplier's liquidity risk `lamS` (`λ_s`), the
retailer's liquidity risk `lamR` (`λ_r`), the range `(Cmin, Cmax)` of credit ratings, the default
probability `ρ` and the interest-rate premium `η` as functions of the credit rating. -/
structure Params where
  c : ℝ
  p : ℝ
  t1 : ℝ
  t2 : ℝ
  lamS : ℝ
  lamR : ℝ
  Cmin : ℝ
  Cmax : ℝ
  ρ : ℝ → ℝ
  η : ℝ → ℝ

/-- Standing assumptions of §3.1–§3.3 (pp. 6074–6076): `0 < c < p`, `t1, t2 > 0`, `λ_s, λ_r ≥ 0`,
`0 ≤ Cmin < Cmax`; on `(Cmin, Cmax)` the default probability `ρ` takes values in `[0, 1]` and is
strictly decreasing, and the premium `η` is positive and (weakly) decreasing. -/
structure Params.Valid (P : Params) : Prop where
  c_pos : 0 < P.c
  c_lt_p : P.c < P.p
  t1_pos : 0 < P.t1
  t2_pos : 0 < P.t2
  lamS_nonneg : 0 ≤ P.lamS
  lamR_nonneg : 0 ≤ P.lamR
  Cmin_nonneg : 0 ≤ P.Cmin
  Cmin_lt_Cmax : P.Cmin < P.Cmax
  ρ_mem : ∀ C ∈ Set.Ioo P.Cmin P.Cmax, P.ρ C ∈ Set.Icc (0 : ℝ) 1
  ρ_strictAnti : StrictAntiOn P.ρ (Set.Ioo P.Cmin P.Cmax)
  η_pos : ∀ C ∈ Set.Ioo P.Cmin P.Cmax, 0 < P.η C
  η_anti : AntitoneOn P.η (Set.Ioo P.Cmin P.Cmax)

/-- The three post-shipment financing schemes: recourse factoring `𝓕`, non-recourse factoring `𝓝`
and reverse factoring `𝓡`. -/
inductive Scheme
  | recourse
  | nonRecourse
  | reverse
  deriving DecidableEq

/-- Tie-breaking rank `𝓡 ≻ 𝓝 ≻ 𝓕`: when two schemes give the supplier the same equilibrium
profit, the higher-ranked one is adopted. -/
def Scheme.rank : Scheme → ℕ
  | .recourse => 0
  | .nonRecourse => 1
  | .reverse => 2

/-- `Λ_𝓕(Cs, Cr) = (1 − ρ_r) + (1 − ρ_s) − e^{η_s t2}` (Eq. (10), p. 6080). -/
noncomputable def coefF (P : Params) (Cs Cr : ℝ) : ℝ :=
  (1 - P.ρ Cr) + (1 - P.ρ Cs) - exp (P.η Cs * P.t2)

/-- `Λ_𝓝(Cr) = e^{−η_r t2}(1 − ρ_r)` (Eq. (10), p. 6080). -/
noncomputable def coefN (P : Params) (Cr : ℝ) : ℝ :=
  exp (-(P.η Cr * P.t2)) * (1 - P.ρ Cr)

/-- `Λ_𝓡 = e^{−η_r(t2 + τ)}` for the payment extension `τ` (p. 6082). -/
noncomputable def coefR (P : Params) (Cr τ : ℝ) : ℝ :=
  exp (-(P.η Cr * (P.t2 + τ)))

/-- The coefficient `Λ_i` of scheme `i` at supplier rating `Cs`, retailer rating `Cr` and payment
extension `τ` (`τ` only matters for reverse factoring). -/
noncomputable def coef (P : Params) : Scheme → ℝ → ℝ → ℝ → ℝ
  | .recourse, Cs, Cr, _ => coefF P Cs Cr
  | .nonRecourse, _, Cr, _ => coefN P Cr
  | .reverse, _, Cr, τ => coefR P Cr τ

/-- Effective unit production cost under recourse factoring,
`c_𝓕 = c e^{(η_s+λ_s)t1} / [(1 − ρ_r) + (1 − ρ_s) − e^{η_s t2}]` (Eq. (8), p. 6078). -/
noncomputable def cF (P : Params) (Cs Cr : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1) / ((1 - P.ρ Cr) + (1 - P.ρ Cs) - exp (P.η Cs * P.t2))

/-- Effective unit production cost under non-recourse factoring,
`c_𝓝 = c e^{(η_s+λ_s)t1 + η_r t2} / (1 − ρ_r)` (Eq. (9), p. 6079). -/
noncomputable def cN (P : Params) (Cs Cr : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1 + P.η Cr * P.t2) / (1 - P.ρ Cr)

/-- Effective unit production cost under reverse factoring with payment extension `τ`,
`c_𝓡(τ) = c e^{(η_s+λ_s)t1 + η_r(t2+τ)}` (Eq. (12), p. 6082). -/
noncomputable def cR (P : Params) (Cs Cr τ : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1 + P.η Cr * (P.t2 + τ))

/-- The effective unit production cost `c_i` of scheme `i`. -/
noncomputable def effCost (P : Params) : Scheme → ℝ → ℝ → ℝ → ℝ
  | .recourse, Cs, Cr, _ => cF P Cs Cr
  | .nonRecourse, Cs, Cr, _ => cN P Cs Cr
  | .reverse, Cs, Cr, τ => cR P Cs Cr τ

/-- The supplier's expected profit under scheme `i` at wholesale price `w` and quantity `q`,
`π_i(q; w) = (1 − ρ_s)(Λ_i e^{−λ_s t1} w S(q) − c q e^{η_s t1})` (Eq. (10), p. 6080; p. 6082 for
reverse factoring). -/
noncomputable def supplierProfit (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : ℝ :=
  (1 - P.ρ Cs) *
    (coef P i Cs Cr τ * exp (-(P.lamS * P.t1)) * w * S μ q - P.c * q * exp (P.η Cs * P.t1))

/-- The retailer's liquidity-benefit factor: `1` under factoring, `2 − e^{−λ_r τ}` under reverse
factoring (p. 6082). -/
noncomputable def retailerFactor (P : Params) : Scheme → ℝ → ℝ
  | .recourse, _ => 1
  | .nonRecourse, _ => 1
  | .reverse, τ => 2 - exp (-(P.lamR * τ))

/-- The retailer's expected profit under scheme `i` at wholesale price `w` when the supplier
produces `q`: `Π_𝓕 = Π_𝓝 = e^{−λ_s t1}(1 − ρ_r)(p − w)S(q)` (pp. 6078, 6079) and
`Π_𝓡 = e^{−λ_s t1}(1 − ρ_r)(2 − e^{−λ_r τ})(p − w)S(q)` (p. 6082, last line of the display). -/
noncomputable def retailerProfit (P : Params) (μ : Measure ℝ) (i : Scheme) (Cr τ w q : ℝ) : ℝ :=
  exp (-(P.lamS * P.t1)) * (1 - P.ρ Cr) * retailerFactor P i τ * (P.p - w) * S μ q

/-- `q` is a best response of the supplier (the follower) to the wholesale price `w`: `q ≥ 0`
maximizes `π_i(·; w)` over all quantities `q' ≥ 0`. -/
def IsBestResponse (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → supplierProfit P μ i Cs Cr τ w q' ≤ supplierProfit P μ i Cs Cr τ w q

/-- Scheme `i` is feasible: some nonnegative wholesale price `w`, together with a best response `q`
of the supplier, gives the retailer a strictly positive expected profit (the physical supply chain
can operate under the scheme, p. 6076). -/
def Feasible (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ : ℝ) : Prop :=
  ∃ w q : ℝ, 0 ≤ w ∧ IsBestResponse P μ i Cs Cr τ w q ∧ 0 < retailerProfit P μ i Cr τ w q

/-- `(w, q)` is a Stackelberg equilibrium of the pull game under scheme `i`: `w ≥ 0`, `q` is a
best response to `w`, and no nonnegative wholesale price `w'`, with any best response `q'` to it,
gives the retailer (the leader) a larger expected profit. -/
def IsEquilibrium (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : Prop :=
  0 ≤ w ∧ IsBestResponse P μ i Cs Cr τ w q ∧
    ∀ w' q' : ℝ, 0 ≤ w' → IsBestResponse P μ i Cs Cr τ w' q' →
      retailerProfit P μ i Cr τ w' q' ≤ retailerProfit P μ i Cr τ w q

/-- Scheme `i` is adopted by the supplier from the set `A` of available schemes: `i ∈ A` is
feasible and has an equilibrium whose supplier profit is at least (if `i` is ranked higher) or
strictly above (if `i` is ranked lower) the supplier's equilibrium profit under every other
feasible scheme `j ∈ A`. Ties are resolved by `Scheme.rank` (`𝓡 ≻ 𝓝 ≻ 𝓕`). -/
def Adopted (P : Params) (μ : Measure ℝ) (A : Set Scheme) (i : Scheme) (Cs Cr τ : ℝ) : Prop :=
  i ∈ A ∧ Feasible P μ i Cs Cr τ ∧
    ∃ w q : ℝ, IsEquilibrium P μ i Cs Cr τ w q ∧
      ∀ j ∈ A, j ≠ i → Feasible P μ j Cs Cr τ →
        ∀ w' q' : ℝ, IsEquilibrium P μ j Cs Cr τ w' q' →
          (j.rank < i.rank →
              supplierProfit P μ j Cs Cr τ w' q' ≤ supplierProfit P μ i Cs Cr τ w q) ∧
          (i.rank < j.rank →
              supplierProfit P μ j Cs Cr τ w' q' < supplierProfit P μ i Cs Cr τ w q)

/-- `x` is the unique value in `(a, b)` satisfying the property `E`: the paper's phrase
"the unique value of `C` that satisfies …". -/
def IsUniqueSolution (a b : ℝ) (E : ℝ → Prop) (x : ℝ) : Prop :=
  x ∈ Set.Ioo a b ∧ E x ∧ ∀ y ∈ Set.Ioo a b, E y → y = x

end SupplyChainFactoring.Choice
