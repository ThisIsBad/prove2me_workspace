import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Theorem 6.1.1 (Bäuerle–Rieder, p. 177, PDF 190). For the multiperiod terminal wealth problem
with partial observation it holds: a) The value functions `J_n(x,ρ)` are strictly increasing,
strictly concave and continuous in `x \in \text{dom } U` for all `ρ \in ℙ(E_Y)`. b) The value
functions can be computed recursively by the Bellman equation, i.e. for `(x,ρ) \in E_X \times
ℙ(E_Y)`: `J_0(x,ρ) = U(x)`, `J_n(x,ρ) = \sup_{a \in D(x)} \int J_{n-1}((1+i)(x+a\cdot z),
Φ(ρ,z)) \, d(\text{predictive }ρ)(z)`. c) The maximal value of problem (6.2) is given by
`J_N(x,Q_0)`. d) There exists a maximiser `f_n^*` of `J_{n-1}` and the portfolio strategy
`(f_0,\dots,f_{N-1})` is optimal for the `N`-stage terminal wealth problem (6.2), where
`f_n(h_n) := f_{N-n}^*(x_n,μ_n(\cdot|h_n))`. `Jsup ... k x ρ` is the value with `k` stages
remaining at belief `ρ` (so `J_0` is the terminal condition, matching the book's own `n`-indexing
where `n` counts stages remaining from the horizon). Part c) ("the maximal value of (6.2) is
`J_N(x,Q_0)`") is not restated as a separate conjunct: `Jsup` is *defined* directly as the
supremum over feasible history-dependent strategies (`HistPolicy`, exactly `Π_N`), so
`Jsup ... N x0 M.Q0` already *is* the value of (6.2) by construction — unlike chunk `05a`/`05b`'s
two-model comparisons (original vs. reduced), this mission uses one unified value-function
scaffold for both roles, so part c)'s content is folded into the definition rather than left as a
gap to close; see `MODERATION_NOTES.md`. All state claims are on `E_X × ℙ(E_Y)` (`x ∈ dom U`,
`ρ` a probability measure), as in the book; part d) states both the existence of measurable,
feasible maximizers `f_k^*` (`f_k^*(x,ρ) ∈ D(x)`) and the optimality of the strategy built from
*any* such choice. -/
theorem theorem_6_1_1 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mk : TerminalWealthMarket M) (N : ℕ) :
    (∀ k ≤ N, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        StrictMonoOn (fun x => Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ) Mk.domU ∧
          (∀ x ∈ Mk.domU, ∀ y ∈ Mk.domU, x ≠ y → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
            (a : EReal) * Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ +
                (b : EReal) * Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k y ρ <
              Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k (a * x + b * y) ρ) ∧
          ContinuousOn (fun x => Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ) Mk.domU) ∧
      (∀ ρ : Measure EY, ∀ x, Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D 0 x ρ = (Mk.U x : EReal)) ∧
      (∀ k < N, ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D (k + 1) x ρ =
        ⨆ a ∈ Mk.D x, erealIntegral (M.predictive ρ) fun z =>
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z)) ∧
      (∃ fs : ℕ → ℝ × Measure EY → Fin d → ℝ,
        ∀ k < N, Measurable (fs k) ∧ ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
          fs k (x, ρ) ∈ Mk.D x ∧
          IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fs k (x, ρ))) ∧
      (∀ fs : ℕ → ℝ × Measure EY → Fin d → ℝ,
        (∀ k < N, Measurable (fs k) ∧ ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
          fs k (x, ρ) ∈ Mk.D x ∧
          IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fs k (x, ρ))) →
        ∀ x0 ∈ Mk.domU, Vpi M Fd (fun _ => Mk.i) Mk.U
            (ofMarkov M Fd (fun _ => Mk.i) x0 fun k xy => fs (N - k) xy) N 0 (fun _ => 0) x0 M.Q0 =
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D N x0 M.Q0) := by sorry

end MDPFinance.POMDPFinance
