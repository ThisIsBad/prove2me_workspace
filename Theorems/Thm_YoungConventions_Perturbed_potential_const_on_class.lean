import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- All states of a recurrent class have the same potential (Young 1993, Econometrica 61:57–84,
Appendix, p. 80, PDF p. 25).

Let `P^ε` be a regular perturbation of the Markov chain `P⁰`. If `x` and `y` lie in the same
recurrent communication class `C` of `P⁰`, then `γ(x) = γ(y)`, with `γ` the potential (9). -/
theorem potential_const_on_class {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (C : Finset X) (hC : C ∈ recurrentClasses P0) (x y : X) (hx : x ∈ C) (hy : y ∈ C) :
    statePotential P x = statePotential P y := by sorry

end YoungConventions.Perturbed

