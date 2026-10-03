import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- `\tilde A := \{α \in ℝ^d \mid 1+α\cdot R(y) \ge 0 \text{ a.s.}\}` for the power-utility case
(Bäuerle–Rieder, p. 178, PDF 191), independent of `y` by Assumption `FM`(ii); quantified over all
`y` for the same reason as `TerminalWealthMarket.D`. -/
def AtildePow (M : FilterMarket EY d) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)), 0 ≤ 1 + ∑ j, a j * z j}

/-- `\tilde A := \{α \mid 1+α\cdot R(y) > 0 \text{ a.s.}\}` for the logarithmic-utility case
(Bäuerle–Rieder, p. 181, PDF 195; the strict inequality, vs. `AtildePow`'s `≥`, is the book's own
distinction between the two utilities' admissible sets). -/
def AtildeLog (M : FilterMarket EY d) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)), 0 < 1 + ∑ j, a j * z j}

/-- The power-utility auxiliary recursion `(d_n)` of (6.3) (Bäuerle–Rieder, Theorem 6.1.2a, p.
178, PDF 191), indexed by stages-remaining `k` (`d_0 \equiv 1/γ`; `d_{k+1}(ρ) := \sup_{α \in
\tilde A} \int d_k(Φ(ρ,z))(1+α\cdot z)^γ \, d(\text{predictive }ρ)(z)`). -/
noncomputable def dPow (M : FilterMarket EY d) (Fd : FilterOp M) (γ : ℝ) :
    ℕ → Measure EY → ℝ
  | 0, _ => 1 / γ
  | (k + 1), ρ =>
      ⨆ a ∈ AtildePow M, ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
        ∂(M.predictive ρ)

/-- The logarithmic-utility auxiliary recursion `(d_n)` of (6.6) (Bäuerle–Rieder, Theorem 6.1.7a,
p. 181, PDF 195), indexed by stages-remaining `k` (`d_0 \equiv 0`; `d_{k+1}(ρ) := \log(1+i) +
\sup_{α \in \tilde A} \int \log(1+α\cdot z) \, d(\text{predictive }ρ)(z) + \int d_k(Φ(ρ,z)) \,
d(\text{predictive }ρ)(z)`), in `[-∞,∞]`: `𝔼 \log(1+α\cdot R)` can be `-∞` for an admissible `α`,
and a real Bochner integral would record it as `0`. -/
noncomputable def dLog (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℝ) :
    ℕ → Measure EY → EReal
  | 0, _ => 0
  | (k + 1), ρ =>
      (Real.log (1 + i) : EReal) +
        (⨆ a ∈ AtildeLog M, erealIntegral (M.predictive ρ) fun z =>
          ((Real.log (1 + ∑ j, a j * z j) : ℝ) : EReal)) +
        erealIntegral (M.predictive ρ) fun z => dLog M Fd i k (Fd.Phi ρ z)

end MDPFinance.POMDPFinance
