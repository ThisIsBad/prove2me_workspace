import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup

/-- The finite-horizon inventory model with advance demand information and set-up costs of
Gallego–Özer (2001), §2 and §4, reduced to the functional equation (8)–(9).

Indices: the lead time is `L`, the information horizon is `N = L + M + 1`, so `N > L + 1`
is `M ≥ 1` (imposed as `[NeZero M]` by the theorems). Periods are `t = 1, …, T`.

* `G t : ℝ → ℝ` — the single-period cost `G_t(y)` of p. 1350, taken as a primitive;
* `K t` — the set-up cost `K_t` (positive: §4 treats positive set-up costs);
* `α t` — the discount factor `α_t`; in (9) period `t` uses `α (t + 1)`;
* `μ t` — the law of the demand vector `D_t = (D_{t,t}, …, D_{t,t+N})`, a measure on
  `Fin (N + 1) → ℝ = Fin (L + M + 2) → ℝ` with component `k` equal to `D_{t,t+k}`.

The hypotheses are those the paper states (`K_t ≥ 0`, here `> 0` by §4; `α_{t+1} K_{t+1} ≤ K_t`;
convex `G_t` with `G_t(y) → ∞` as `|y| → ∞`) and those it uses without stating: positive
discount factors, nonnegative demands, finite first moments of the demands and at most linear
growth of `G_t` (so that the expectation in (9) is finite). -/
structure Model (L M : ℕ) where
  /-- The planning horizon `T`. -/
  T : ℕ
  /-- Single-period cost `G_t`. -/
  G : ℕ → ℝ → ℝ
  /-- Set-up cost `K_t`. -/
  K : ℕ → ℝ
  /-- Discount factor `α_t`. -/
  α : ℕ → ℝ
  /-- Law of the demand vector `D_t`. -/
  μ : ℕ → Measure (Fin (L + M + 2) → ℝ)
  G_convex : ∀ t, ConvexOn ℝ Set.univ (G t)
  G_coercive : ∀ t, Tendsto (G t) (cocompact ℝ) atTop
  G_linearGrowth : ∀ t, ∃ a b : ℝ, ∀ y, |G t y| ≤ a + b * |y|
  K_pos : ∀ t, 0 < K t
  α_pos : ∀ t, 0 < α t
  discount_setup : ∀ t, α (t + 1) * K (t + 1) ≤ K t
  μ_prob : ∀ t, IsProbabilityMeasure (μ t)
  μ_nonneg : ∀ t, ∀ᵐ D ∂(μ t), ∀ k, 0 ≤ D k
  μ_integrable : ∀ t, ∀ k, Integrable (fun D : Fin (L + M + 2) → ℝ => D k) (μ t)

variable {L M : ℕ}

/-- The observed demand `o_{t,t+L+1+j}` for `j < M`, extended by `0` for `j ≥ M`
(the paper sets `O_{t,s} ≡ 0` for `s ≥ t + N`, p. 1347). -/
def obsComp (o : Fin M → ℝ) (j : ℕ) : ℝ :=
  if h : j < M then o ⟨j, h⟩ else 0

/-- Transition (5) of the modified inventory position: after ordering up to `y` and observing
`D = D_t`, `x_{t+1} = y - D_{t,t} - ∑_{s=t+1}^{t+L+1} D_{t,s} - o_{t,t+L+1}`, i.e.
`y - ∑_{k=0}^{L+1} D k - o 0`. -/
def nextX (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) : ℝ :=
  y - ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k) - obsComp o 0

/-- Transition (6) of the observed demand beyond the protection period:
`O_{t+1,s} = O_{t,s} + D_{t,s}` for `s = t+L+2, …, t+N`, i.e. component `j` of the new vector is
`o (j + 1) + D (L + 2 + j)`, with `o M = O_{t,t+N} = 0`. -/
def nextO (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) : Fin M → ℝ :=
  fun j => obsComp o (j.val + 1) + D ⟨L + 2 + j.val, by have := j.isLt; omega⟩

/-- Backward recursion on the number of remaining periods: `P.Jgo n` is `J_{T+1-n}`.
`Jgo 0 = J_{T+1} ≡ 0`, and with `n + 1` periods remaining the current period is `t = T - n`,
where `J_t(x, o) = min_{y ≥ x} {K_t δ(y - x) + V_t(y, o)}` (8) and
`V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})` (9), the expectation being over
`D_t ∼ μ_t`. -/
noncomputable def Model.Jgo (P : Model L M) : ℕ → ℝ → (Fin M → ℝ) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x o =>
      orderCost (P.K (P.T - n))
        (fun y => P.G (P.T - n) y + P.α (P.T - n + 1) *
          ∫ D, P.Jgo n (nextX y o D) (nextO o D) ∂(P.μ (P.T - n))) x

/-- The optimal cost `J_t(x, o)` of (8), for periods `1 ≤ t ≤ T`; `J_{T+1} ≡ 0`. -/
noncomputable def Model.J (P : Model L M) (t : ℕ) : ℝ → (Fin M → ℝ) → ℝ :=
  P.Jgo (P.T + 1 - t)

/-- The cost-to-go `V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})` of (9). -/
noncomputable def Model.V (P : Model L M) (t : ℕ) (y : ℝ) (o : Fin M → ℝ) : ℝ :=
  P.G t y + P.α (t + 1) * ∫ D, P.J (t + 1) (nextX y o D) (nextO o D) ∂(P.μ t)

/-- `H_t(x, o) = K_t + min_{y ≥ x} V_t(y, o) - V_t(x, o)` (p. 1350). -/
noncomputable def Model.H (P : Model L M) (t : ℕ) (x : ℝ) (o : Fin M → ℝ) : ℝ :=
  reorderGap (P.K t) (fun y => P.V t y o) x

/-- `J_{T+1} ≡ 0`. -/
theorem Model.J_terminal (P : Model L M) (x : ℝ) (o : Fin M → ℝ) : P.J (P.T + 1) x o = 0 := by
  simp [Model.J, Model.Jgo]

/-- The functional equation (8): for `1 ≤ t ≤ T`,
`J_t(x, o) = min_{y ≥ x} {K_t δ(y - x) + V_t(y, o)}`. -/
theorem Model.J_eq (P : Model L M) (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ P.T) (x : ℝ)
    (o : Fin M → ℝ) : P.J t x o = orderCost (P.K t) (fun y => P.V t y o) x := by
  have h1 : P.T + 1 - t = (P.T - t) + 1 := by omega
  have h2 : P.T - (P.T - t) = t := by omega
  have h3 : P.T + 1 - (t + 1) = P.T - t := by omega
  simp only [Model.J, Model.V, h1, Model.Jgo, h2, h3]

end GallegoOzerADI.PositiveSetup
