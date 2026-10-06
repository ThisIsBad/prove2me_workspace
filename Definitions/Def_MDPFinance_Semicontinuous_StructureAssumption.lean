import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered), restated from
`MDPFinance.Bellman.StructureAssumption` (chunk `02a`): there exist sets `IM_n ⊆ IM(E)` and
`Δ_n ⊆ F_n` such that (i) `g_N ∈ IM_N`, (ii) if `v ∈ IM_{n+1}` then `T_n v ∈ IM_n`, and (iii)
for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with `f_n ∈ Δ_n`, for
`n = 0, …, N-1`. This chunk's goal (Theorem 2.4.13) and its supporting milestones each exhibit
concrete `IM_n`, `Δ_n` satisfying this same predicate. -/
def StructureAssumption (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal))
    (Deltas : ℕ → Set (E → A)) : Prop :=
  (∀ n, IMs n ⊆ IM E) ∧
  (∀ n < N, Deltas n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, IsMaximizer M n v f)

end MDPFinance.Semicontinuous
