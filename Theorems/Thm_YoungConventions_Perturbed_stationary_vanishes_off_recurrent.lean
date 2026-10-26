import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain

namespace YoungConventions.Perturbed

/-- Stationary distributions vanish off the recurrent states (Young 1993, Econometrica 61:57–84,
Appendix, p. 80, PDF p. 25: "Since μ⁰ is a stationary distribution of P⁰, μ⁰_z = 0 for every
state z that is not recurrent under P⁰").

For every Markov chain `A` on a finite set `X`, every stationary distribution `ν` of `A` and
every state `z` that is not recurrent under `A`, `ν z = 0`.

**Formalization Note.** The page applies this to `μ⁰` and `P⁰`; it is stated here for an arbitrary
finite chain, which is the fact used. -/
theorem stationary_vanishes_off_recurrent {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (ν : X → ℝ) (hν : IsStationaryDist A ν) (z : X) (hz : ¬ IsRecurrentState A z) :
    ν z = 0 := by sorry

end YoungConventions.Perturbed

