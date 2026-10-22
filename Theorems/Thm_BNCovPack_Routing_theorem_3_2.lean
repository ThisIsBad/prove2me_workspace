import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_FracScheme

namespace BNCovPack.Routing

/-- Theorem 3.2 (packing half, with the oracle remark), Buchbinder–Naor 2009, p. 5, on the
routing problem of §5.2 (Fig. 3, p. 14). Let `E` be a finite set of edges with capacities
`u e > 0`, let every path of every request have at most `Pmax` edges, and run the `{0,1}`
fractional scheme with `ℓ = Pmax + 1` and `B' = 2 ln(1 + ℓ) = 2 ln(Pmax + 2)` on the request
sequence `σ`. Then the flows it produces form a feasible fractional routing of `σ`, and every
feasible fractional routing `f` of `σ` has value at most `2 ln(Pmax + 2)` times the scheme's. -/
theorem theorem_3_2 {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (hu : ∀ e, 0 < u e)
    (Pmax : ℕ) (σ : List (List (Finset E))) (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    IsFeasibleRouting u σ (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f ≤ 2 * Real.log ((Pmax : ℝ) + 2) *
        routingValue (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows := by sorry

end BNCovPack.Routing

