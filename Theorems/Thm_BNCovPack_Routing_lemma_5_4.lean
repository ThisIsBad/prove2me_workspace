import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_Potential
import Definitions.Def_BNCovPack_Routing_Algorithm

namespace BNCovPack.Routing

/-- Lemma 5.4, Buchbinder–Naor 2009, p. 16 (explicit form from the proof, pp. 16–17). Let `E` be
a non-empty finite set of `m` edges with capacities `u e > 0`, let every path of every request in
`σ` have at most `Pmax` edges, and let `B = exp(1 + ln(2m)/u(min)) − 1`. After the online routing
algorithm of §5.2 has processed `σ`:
1. no capacity is violated: `χ(e) ≤ u(e)` for every edge `e`;
2. the number of served requests is at least `OPT/(4 B ln 2 · ln(Pmax + 2)) − 1`, where `OPT` is the
   value of any feasible fractional routing of `σ`. -/
theorem lemma_5_4 {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (hu : ∀ e, 0 < u e) (Pmax : ℕ) (σ : List (List (Finset E)))
    (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    (∀ e, ((algorithm u Pmax σ).chi e : ℝ) ≤ u e) ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f / (4 * roundingScale u * Real.log 2 * Real.log ((Pmax : ℝ) + 2)) - 1 ≤
        ((algorithm u Pmax σ).served : ℝ) := by sorry

end BNCovPack.Routing

