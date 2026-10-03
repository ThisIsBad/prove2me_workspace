import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- The (stationary) terminal-wealth market of §6.1 (Bäuerle–Rieder, p. 177-178, PDF 190-191):
utility `U : \text{dom } U → ℝ` (strictly increasing, strictly concave, continuous), constant rate
`i`, feasible set `D(x) := \{a \mid (1+i)(x+a\cdot z) \in \text{dom } U \text{ for } q_R(y,\cdot)
\text{-a.e. } z, \text{ every } y\}` (`FM`(ii): the support of `R(y)` is independent of `y`, so
quantifying `∀ y` is faithful and well-defined, matching the book's own remark just after the
model's bullet list). `dom U = [0,∞)` or `(0,∞)`, `1+i > 0`, and the section's standing
Assumption (FM) (p. 176) are fields. -/
structure TerminalWealthMarket (M : FilterMarket EY d) where
  domU : Set ℝ
  hdomU : domU = Set.Ici 0 ∨ domU = Set.Ioi 0
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U domU
  hU_concave : StrictConcaveOn ℝ domU U
  hU_cont : ContinuousOn U domU
  i : ℝ
  hi_pos : 0 < 1 + i
  /-- Assumption (FM)(i): no arbitrage, for every hidden state `y`. -/
  hNA : ∀ y (φ : Fin d → ℝ), (∀ᵐ z ∂(M.law y), 0 ≤ ∑ j, φ j * z j) →
    ∀ᵐ z ∂(M.law y), ∑ j, φ j * z j = 0
  /-- Assumption (FM)(ii): the support of `R(y)` is independent of `y` — made precise as the
  laws having the same null sets, which is what makes the a.s. conditions in `D(x)` and `Ã`
  independent of the unobserved `y`. -/
  hsupp : ∀ y y', M.law y ≪ M.law y'
  /-- Assumption (FM)(iii): `sup_y 𝔼‖R(y)‖ < ∞`. -/
  hmom : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ y, ∫⁻ z, ‖z‖ₑ ∂(M.law y) ≤ K

variable {M : FilterMarket EY d}

/-- `D(x) := \{a \in ℝ^d \mid (1+i)(x+a\cdot z) \in \text{dom } U\}` for `q_R(y,\cdot)`-a.e. `z`,
for every `y \in E_Y` (Bäuerle–Rieder, p. 177). -/
def TerminalWealthMarket.D (Mk : TerminalWealthMarket M) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)),
    (1 + Mk.i) * (x + ∑ j, a j * z j) ∈ Mk.domU}

end MDPFinance.POMDPFinance
