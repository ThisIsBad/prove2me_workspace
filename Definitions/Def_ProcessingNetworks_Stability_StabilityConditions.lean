import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open Classical in
/-- Taboo transition probabilities of the jump chain: `tabooProb jump x n y` is the probability
that the chain driven by `jump`, started at `x`, is at `y` after `n` steps without having returned
to `x` at any of the steps `1, …, n` (so `tabooProb jump x 0 y = [y = x]`). -/
noncomputable def tabooProb {X : Type*} (jump : X → PMF X) (x : X) : ℕ → X → ℝ≥0∞
  | 0, y => if y = x then 1 else 0
  | n + 1, y => if y = x then 0 else ∑' z : X, tabooProb jump x n z * jump z y

/-- Probability that the jump chain started at `x` first returns to `x` at step `n + 1`
(`N_x = n + 1` in Eq. (D.16)). -/
noncomputable def firstReturnProb {X : Type*} (jump : X → PMF X) (x : X) (n : ℕ) : ℝ≥0∞ :=
  ∑' z : X, tabooProb jump x n z * jump z x

/-- The state `x` is recurrent (Definition D.7, through the jump chain, as the book does): the
chain started at `x` returns to `x` with probability one. -/
def Recurrent {X : Type*} (jump : X → PMF X) (x : X) : Prop :=
  ∑' n : ℕ, firstReturnProb jump x n = 1

/-- Expected first passage time `E_x(T_x)` of the continuous-time chain back to `x` (Eq. (D.15)),
computed through the sample-path construction (D.5)–(D.6): the chain holds for an independent
unit-mean exponential clock divided by `λ(y)` at every state `y` its jump chain visits before the
first return, so `E_x(T_x) = ∑ₙ ∑ᵧ P_x(Yₙ = y, n < N_x) / λ(y)`. -/
noncomputable def meanReturnTime {X : Type*} (jump : X → PMF X) (rate : X → ℝ) (x : X) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' y : X, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹

/-- Positive recurrence of the continuous-time chain with jump matrix `jump` and exit rates `rate`
(Definition D.15): every state is recurrent with finite mean return time `E_x(T_x) < ∞`. -/
def PositiveRecurrent {X : Type*} (jump : X → PMF X) (rate : X → ℝ) : Prop :=
  ∀ x : X, Recurrent jump x ∧ meanReturnTime jump rate x < ⊤

/-- `π` is a stationary distribution for the continuous-time chain (Definition D.16): `π Λ = 0`
for the generator `Λ` with off-diagonal entries `Λ(x, y) = λ(x) G(x, y)` and diagonal
`Λ(y, y) = -λ(y)`; written out (Lemma D.9), `∑ₓ π(x) λ(x) G(x, y) = π(y) λ(y)` for every `y`. -/
def IsStationaryDistribution {X : Type*} (jump : X → PMF X) (rate : X → ℝ) (π : PMF X) : Prop :=
  ∀ y : X, ∑' x : X, π x * ENNReal.ofReal (rate x) * jump x y = π y * ENNReal.ofReal (rate y)

/-- The chain has a unique stationary distribution (Proposition 3.5(b)). -/
def HasUniqueStationaryDistribution {X : Type*} (jump : X → PMF X) (rate : X → ℝ) : Prop :=
  ∃! π : PMF X, IsStationaryDistribution jump rate π

/-- The buffer-contents process `Z` converges in distribution to a non-defective limit
(Proposition 3.5(c)): there is a genuine probability distribution `π` on `Z^I_+` (a `PMF`, hence
automatically non-defective) such that, for every `z`, `P(Z(t) = z) → π(z)` as `t → ∞`. -/
def ConvergesInDistribution {Ω : Type*} [MeasureSpace Ω] {I : ℕ} (Z : ℝ → Ω → Fin I → ℕ) : Prop :=
  ∃ π : PMF (Fin I → ℕ), ∀ z : Fin I → ℕ,
    Filter.Tendsto (fun t : ℝ => (ℙ {ω | Z t ω = z}).toReal) Filter.atTop (nhds (π z).toReal)

end ProcessingNetworks.Stability
