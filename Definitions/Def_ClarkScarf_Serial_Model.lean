import Mathlib

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- The data of the two-installation serial inventory model of Clark and Scarf (1960), §§2–3,
with its standing hypotheses. Installation 1 faces the demand; installation 2 supplies it with a
lead time of two periods; system (echelon 2) orders arrive after one period.

* `h`, `p`: marginal holding and shortage cost at installation 1, eq. (1);
* `α`: the discount factor;
* `c1`: unit shipping cost from installation 2 to installation 1;
* `K`, `c`: setup and unit cost of the echelon-2 order cost (5);
* `φ`: the demand density on `(0, ∞)`;
* `Lt`: `L̃`, the natural one-period cost at echelon 2 (Assumption 3). -/
structure Model where
  h : ℝ
  p : ℝ
  α : ℝ
  c1 : ℝ
  K : ℝ
  c : ℝ
  φ : ℝ → ℝ
  Lt : ℝ → ℝ
  h_nonneg : 0 ≤ h
  p_nonneg : 0 ≤ p
  α_nonneg : 0 ≤ α
  c1_nonneg : 0 ≤ c1
  K_nonneg : 0 ≤ K
  c_nonneg : 0 ≤ c
  φ_nonneg : ∀ t, 0 ≤ φ t
  φ_total : ∫ t in Ioi (0 : ℝ), φ t = 1
  φ_mean : IntegrableOn (fun t => t * φ t) (Ioi (0 : ℝ))
  Lt_nonneg : ∀ x, 0 ≤ Lt x
  Lt_cont : Continuous Lt
  Lt_growth : ∃ a b : ℝ, ∀ x, Lt x ≤ a + b * |x|

namespace Model

/-- The expected one-period holding and shortage cost (1) at installation 1, as a function of the
stock on hand `x` at the beginning of the period. -/
noncomputable def L (M : Model) (x : ℝ) : ℝ :=
  if 0 < x then M.h * x + M.p * ∫ t in Ioi x, (t - x) * M.φ t
  else M.p * ∫ t in Ioi (0 : ℝ), (t - x) * M.φ t

/-- The echelon-2 order cost (5): `c(z) = K + c z` for `z > 0` and `c(0) = 0`. -/
noncomputable def orderCost (M : Model) (z : ℝ) : ℝ :=
  if 0 < z then M.K + M.c * z else 0

/-- `Ĉ_n(x₁, w₁)`, the optimal `n`-period cost of installation 1 in isolation, eq. (15):
`Ĉ_0 ≡ 0` and `Ĉ_{n+1}(x₁, w₁) = inf_{y ≥ x₁ + w₁} {c₁(y - x₁ - w₁) + L(x₁)
+ α ∫₀^∞ Ĉ_n(x₁ + w₁ - t, y - x₁ - w₁) φ(t) dt}`. -/
noncomputable def isoCost (M : Model) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x₁ w₁ => ⨅ y : {y : ℝ // x₁ + w₁ ≤ y},
      (M.c1 * ((y : ℝ) - x₁ - w₁) + M.L x₁ +
        M.α * ∫ t in Ioi (0 : ℝ), isoCost M n (x₁ + w₁ - t) ((y : ℝ) - x₁ - w₁) * M.φ t)

/-- The expression in braces of (15) for `n + 1` periods remaining, as a function of the target
`y` of stock on hand plus in transit at installation 1. -/
noncomputable def isoObj (M : Model) (n : ℕ) (x₁ w₁ y : ℝ) : ℝ :=
  M.c1 * (y - x₁ - w₁) + M.L x₁ +
    M.α * ∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (y - x₁ - w₁) * M.φ t

theorem isoCost_succ (M : Model) (n : ℕ) (x₁ w₁ : ℝ) :
    M.isoCost (n + 1) x₁ w₁ = ⨅ y : {y : ℝ // x₁ + w₁ ≤ y}, M.isoObj n x₁ w₁ y := rfl

/-- `C_n(x₁, w₁, x₂)`, the optimal `n`-period system cost, eq. (14): `C_0 ≡ 0` and
`C_{n+1}(x₁, w₁, x₂) = inf_{x₁ + w₁ ≤ y ≤ x₂, 0 ≤ z} {c(z) + c₁(y - x₁ - w₁) + L̃(x₂) + L(x₁)
+ α ∫₀^∞ C_n(x₁ + w₁ - t, y - x₁ - w₁, x₂ + z - t) φ(t) dt}`. The pair `q` is `(y, z)`. -/
noncomputable def sysCost (M : Model) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0 => fun _ _ _ => 0
  | n + 1 => fun x₁ w₁ x₂ =>
      ⨅ q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
        (M.orderCost (q : ℝ × ℝ).2 + M.c1 * ((q : ℝ × ℝ).1 - x₁ - w₁) + M.Lt x₂ + M.L x₁ +
          M.α * ∫ t in Ioi (0 : ℝ),
            sysCost M n (x₁ + w₁ - t) ((q : ℝ × ℝ).1 - x₁ - w₁) (x₂ + (q : ℝ × ℝ).2 - t) *
              M.φ t)

/-- The expression in braces of (14) for `n + 1` periods remaining, as a function of the
installation-1 target `y` and the system order quantity `z`. -/
noncomputable def sysObj (M : Model) (n : ℕ) (x₁ w₁ x₂ y z : ℝ) : ℝ :=
  M.orderCost z + M.c1 * (y - x₁ - w₁) + M.Lt x₂ + M.L x₁ +
    M.α * ∫ t in Ioi (0 : ℝ), M.sysCost n (x₁ + w₁ - t) (y - x₁ - w₁) (x₂ + z - t) * M.φ t

theorem sysCost_succ (M : Model) (n : ℕ) (x₁ w₁ x₂ : ℝ) :
    M.sysCost (n + 1) x₁ w₁ x₂ =
      ⨅ q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
        M.sysObj n x₁ w₁ x₂ (q : ℝ × ℝ).1 (q : ℝ × ℝ).2 := rfl

/-- `f_n(u)` of (7), the part of the isolated cost of installation 1 that a shipment can
modify: `f_n ≡ 0` for `n ≤ 2` (no shipment arrives within the horizon), and for `n + 3` periods
`f_{n+3}(u) = inf_{y ≥ u} {c₁(y - u) + α² ∫₀^∞∫₀^∞ L(y - t₁ - t₂) φ(t₁) φ(t₂) dt₂ dt₁
+ α ∫₀^∞ f_{n+2}(y - t) φ(t) dt}`. -/
noncomputable def fLag (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 0
  | 2 => fun _ => 0
  | n + 3 => fun u => ⨅ y : {y : ℝ // u ≤ y},
      (M.c1 * ((y : ℝ) - u) +
        M.α ^ 2 * (∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
          M.L ((y : ℝ) - t₁ - t₂) * M.φ t₁ * M.φ t₂) +
        M.α * ∫ t in Ioi (0 : ℝ), fLag M (n + 2) ((y : ℝ) - t) * M.φ t)

/-- `x̄` is a single critical number of the isolated installation-1 problem (15) with `n + 1`
periods remaining: ordering up to `x̄` when `x₁ + w₁ < x̄`, and not ordering otherwise, attains the
infimum in (15) at every state. -/
def IsCriticalNumber (M : Model) (n : ℕ) (xbar : ℝ) : Prop :=
  ∀ x₁ w₁ y : ℝ, x₁ + w₁ ≤ y → M.isoObj n x₁ w₁ (max (x₁ + w₁) xbar) ≤ M.isoObj n x₁ w₁ y

/-- `Λ(x₂)` of (25), the augmentation of the echelon-2 natural cost, for `n + 1` periods remaining
with critical number `x̄`: for `n ≥ 2` and `x₂ < x̄`,
`Λ(x₂) = c₁(x₂ - x̄) + α² ∫₀^∞∫₀^∞ [L(x₂ - t - y) - L(x̄ - t - y)] φ(t) φ(y) dy dt
+ α ∫₀^∞ [f_n(x₂ - t) - f_n(x̄ - t)] φ(t) dt`, and `Λ(x₂) = 0` otherwise. -/
noncomputable def Lambda (M : Model) (n : ℕ) (xbar x₂ : ℝ) : ℝ :=
  if 2 ≤ n ∧ x₂ < xbar then
    M.c1 * (x₂ - xbar) +
      M.α ^ 2 * (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) +
      M.α * ∫ t in Ioi (0 : ℝ), (M.fLag n (x₂ - t) - M.fLag n (xbar - t)) * M.φ t
  else 0

/-- The functions `g_n(x₂)` of (26), given critical numbers `xbar (n + 1)` for `n + 1` periods
remaining: `g_0 ≡ 0` and `g_{n+1}(x₂) = inf_{z ≥ 0} {c(z) + L̃(x₂) + Λ(x₂)
+ α ∫₀^∞ g_n(x₂ + z - t) φ(t) dt}` with `Λ` taken for `n + 1` periods and `x̄ = xbar (n + 1)`. -/
noncomputable def gClark (M : Model) (xbar : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x₂ => ⨅ z : {z : ℝ // 0 ≤ z},
      (M.orderCost (z : ℝ) + M.Lt x₂ + M.Lambda n (xbar (n + 1)) x₂ +
        M.α * ∫ t in Ioi (0 : ℝ), gClark M xbar n (x₂ + (z : ℝ) - t) * M.φ t)

end Model

end ClarkScarf.Serial
