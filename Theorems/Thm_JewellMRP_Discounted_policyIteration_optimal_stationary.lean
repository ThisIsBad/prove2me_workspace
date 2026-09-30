import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- p. 947 with Claims (a)–(d) of p. 946: for `α > 0`, the value-determination equations (15)
of every stationary policy are uniquely solvable, and every run of the algorithm of Fig. 1
reaches two identical successive policies `d K = d (K + 1)` within at most `Z^N` cycles; the
stationary policy `d K` then has limiting return `v K`, which is at least the limiting return
of every nonstationary policy and equals the limit of the optimal `n`-step returns of (6). -/
theorem policyIteration_optimal_stationary {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    (∀ d : S → A, ∃! v : S → ℝ, SolvesEval M α d v) ∧
    ∀ (d : ℕ → S → A) (v : ℕ → S → ℝ), IsFig1Run M α d v →
      ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K ∧
        (∀ V0 : S → ℝ,
          Tendsto (fun n => policyReturn M α (fun _ => d K) V0 n) atTop (𝓝 (v K))) ∧
        (∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
          Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v K i) ∧
        (∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 (v K))) := by sorry

end JewellMRP.Discounted

