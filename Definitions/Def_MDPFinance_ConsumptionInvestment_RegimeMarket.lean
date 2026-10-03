import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- The stationary regime-switching consumption-investment Markov Decision Model
(Bäuerle–Rieder, p. 100-102, PDF 114-116): state space `E := [0,∞) × E_Y` (wealth, environment
regime), action space `ℝ_{\ge0} × ℝ^d`, transition `T((x,j),(c,a),(z,k)) := ((1+i)(x-c+a·z), k)`
where `(z,k)` has law `Q_j(dz) p_{jk}` given current regime `j`; `r((x,j),(c,a)) := U_c(c)`,
`g(x,j) := U_p(x)`; discount `β ∈ (0,1]`. `E_Y` is a finite set of regimes, `p_{jk}` the Markov
chain's transition probabilities, `Q_j` the regime-conditional law of the relative risk. The
section's standing assumptions are carried: `1 + i > 0`, `dom U_c = dom U_p = [0,∞)`, and
Assumption (FM): (i) no arbitrage in every regime (`φ·R(j) ≥ 0` a.s. implies `φ·R(j) = 0` a.s.),
(ii) `𝔼‖R(j)‖ < ∞`. -/
structure RegimeSwitchingMarket (EY : Type*) [Fintype EY] [MeasurableSpace EY] (d : ℕ) where
  i : ℝ
  hi_pos : 0 < 1 + i
  β : ℝ
  hβ_pos : 0 < β
  hβ_le_one : β ≤ 1
  p : EY → EY → ℝ
  hp_nonneg : ∀ j k, 0 ≤ p j k
  hp_sum : ∀ j, ∑ k, p j k = 1
  Q : EY → Measure (Fin d → ℝ)
  hQ_prob : ∀ j, IsProbabilityMeasure (Q j)
  hNA : ∀ j, ¬ ∃ a : Fin d → ℝ, (∀ᵐ z ∂(Q j), 0 ≤ ∑ k, a k * z k) ∧
    Q j {z | 0 < ∑ k, a k * z k} > 0
  hFM2 : ∀ j, Integrable (fun z => ∑ k, |z k|) (Q j)
  domU : Set ℝ
  hdomU : domU = Set.Ici 0
  Uc : ℝ → ℝ
  Up : ℝ → ℝ
  hUc_mono : StrictMonoOn Uc domU
  hUc_concave : StrictConcaveOn ℝ domU Uc
  hUc_cont : ContinuousOn Uc domU
  hUp_mono : StrictMonoOn Up domU
  hUp_concave : StrictConcaveOn ℝ domU Up
  hUp_cont : ContinuousOn Up domU

variable {EY : Type*} [Fintype EY] [MeasurableSpace EY] {d : ℕ}

/-- The admissible actions `D(x,j) := {(c,a) | 0 ≤ c ≤ x, (1+i)(x-c+a·z) ∈ domU  Q_j-a.e. z}`
(Bäuerle–Rieder, p. 102, PDF 116). -/
def RegimeSwitchingMarket.D (M : RegimeSwitchingMarket EY d) (x : ℝ) (j : EY) :
    Set (ℝ × (Fin d → ℝ)) :=
  {ca | 0 ≤ ca.1 ∧ ca.1 ≤ x ∧ ca.1 ∈ M.domU ∧
    ∀ᵐ z ∂(M.Q j), (1 + M.i) * (x - ca.1 + ∑ k, ca.2 k * z k) ∈ M.domU}

/-- A policy sequence `π : ℕ → ℝ × E_Y → ℝ × ℝ^d` is admissible over the first `n` stages if
`π l` is measurable and `π l (x,j) ∈ D(x,j)` for every `l < n`, every state `x ∈ E = domU` and
every regime `j` (Bäuerle–Rieder, p. 102, PDF 116: the stage-`n` decision rule may depend on `n`
even though the model itself is stationary). -/
def RegimeSwitchingMarket.IsAdmissible (M : RegimeSwitchingMarket EY d) (n : ℕ)
    (π : ℕ → ℝ × EY → ℝ × (Fin d → ℝ)) : Prop :=
  ∀ l < n, (∀ x ∈ M.domU, ∀ j, π l (x, j) ∈ M.D x j) ∧ Measurable (π l)

/-- Auxiliary accumulator for the expected discounted reward-to-go under a fixed policy sequence
`π`, from state `(x,j)`, with `steps` stages to go (Bäuerle–Rieder, p. 102, PDF 116, the display
before Theorem 4.4.1: `J_n(x,j) := sup_π 𝔼^π_{xj}[Σ_{l=0}^{n-1} β^l U_c(c_l(X_l,Y_l)) +
β^n U_p(X_n)]`): the next regime is averaged with `p_{j·}` and the relative risk integrated
against `Q_j`, in `[-∞, ∞)`. -/
noncomputable def RegimeSwitchingMarket.EFromToAcc (M : RegimeSwitchingMarket EY d)
    (π : ℕ → ℝ × EY → ℝ × (Fin d → ℝ)) :
    (steps : ℕ) → (x : ℝ) → (j : EY) → (acc : ℝ) → (disc : ℝ) → EReal
  | 0, x, _, acc, disc => ((acc + disc * M.Up x : ℝ) : EReal)
  | (steps + 1), x, j, acc, disc =>
      let c := (π 0 (x, j)).1
      let a := (π 0 (x, j)).2
      ∑ l, (M.p j l : EReal) * erealIntegral (M.Q j) (fun z =>
        M.EFromToAcc (fun k => π (k + 1)) steps
          ((1 + M.i) * (x - c + ∑ m, a m * z m)) l (acc + disc * M.Uc c) (disc * M.β))

/-- The value `J_n^π(x,j)` of policy sequence `π` over `n` stages, from `(x,j)`
(Bäuerle–Rieder, p. 102, PDF 116). -/
noncomputable def RegimeSwitchingMarket.Jpi (M : RegimeSwitchingMarket EY d)
    (π : ℕ → ℝ × EY → ℝ × (Fin d → ℝ)) (n : ℕ) (x : ℝ) (j : EY) : EReal :=
  M.EFromToAcc π n x j 0 1

/-- The value function `J_n(x,j) := sup_π J_n^π(x,j)` over admissible policy sequences
(Bäuerle–Rieder, p. 102, PDF 116). -/
noncomputable def RegimeSwitchingMarket.J (M : RegimeSwitchingMarket EY d) (n : ℕ) (x : ℝ)
    (j : EY) : EReal :=
  ⨆ π ∈ {π : ℕ → ℝ × EY → ℝ × (Fin d → ℝ) | M.IsAdmissible n π}, M.Jpi π n x j

end MDPFinance.ConsumptionInvestment
