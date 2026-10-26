import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation

open Filter Topology

namespace YoungConventions.Perturbed

/-- Resistance is well defined, and zero resistance means feasible under `P⁰`
(Young 1993, Econometrica 61:57–84, Appendix, discussion of condition (8), p. 77, PDF p. 22).

For a regular perturbation `P^ε` of a Markov chain `P⁰` and all states `x, y`:
1. the exponent `r` of (8) is unique;
2. if `P^ε_{xy} > 0` for some `ε ∈ (0, a]`, then `(x, y)` is an edge of `G` (positive for all
   sufficiently small `ε`);
3. on an edge of `G`, `resistance P x y` is an exponent satisfying (8);
4. `(x, y)` is an edge of `G` of zero resistance iff `P⁰_{xy} > 0`.

**Formalization Note.** Item 4 is the paper's "r(x, y) = 0 if and only if P⁰_xy > 0", read on the
transitions for which `r(x, y)` is defined (the edges of `G`); together with item 2 it also gives
`P⁰_{xy} = 0` whenever `(x, y)` is not an edge of `G`. -/
theorem resistance_spec {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X) :
    (∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r') ∧
    ((∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y) ∧
    (IsEdge P x y → HasResistance P x y (resistance P x y)) ∧
    ((IsEdge P x y ∧ resistance P x y = 0) ↔ 0 < P0 x y) := by sorry

end YoungConventions.Perturbed

