import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered): there exist sets
`IM_n ⊆ IM(E)` and `Δ_n ⊆ F_n` such that (i) `g_N ∈ IM_N`, (ii) if `v ∈ IM_{n+1}` then
`T_n v ∈ IM_n`, and (iii) for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with
`f_n ∈ Δ_n`, for `n = 0, …, N-1`. `IMs : ℕ → Set (E → EReal)` and `Deltas : ℕ → Set (E → A)`
play the roles of `(IM_n)` and `(Δ_n)`; the containments `IM_n ⊆ IM(E)` and `Δ_n ⊆ F_n` are
recorded as explicit hypotheses rather than folded into the membership clauses, matching the
book's own two-step phrasing ("There exist sets `IM_n ⊂ IM(E)` and `Δ_n ⊂ F_n` such that…"). -/
def StructureAssumption (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal))
    (Deltas : ℕ → Set (E → A)) : Prop :=
  (∀ n, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end MDPFinance.Bellman
