import Definitions.Def_fep_finite_information

/-!
# Finite generative model and posterior-form variational free energy

Transcribed from the proved module `FepSketches.active_inference` of the
fep_lean formalization (Active Inference Institute).  One policy-conditioned
carrier owns prediction, observation, posterior state, preferences, and the
posterior-form variational free energy.  The epistemic sign is fixed by
definition; the theorems of this mission derive the surprisal bound, its
exactness at the Bayesian posterior, its uniqueness characterization, and the
evidence lower bound.
-/

namespace FreeEnergyPrinciple

open Finset
open scoped BigOperators

variable {Policy State Outcome : Type*}
  [Fintype Policy] [Fintype State] [Fintype Outcome]

/-- Finite policy-conditioned generative model for active inference. -/
structure GenerativeModel (Policy State Outcome : Type*)
    [Fintype Policy] [Fintype State] [Fintype Outcome] where
  initialState : FiniteLaw State
  transition : Policy → FiniteKernel State State
  likelihood : FiniteKernel State Outcome
  preferences : FiniteLaw Outcome
  policyPrior : FiniteLaw Policy

/-- State prediction under a candidate policy. -/
def predictedState (model : GenerativeModel Policy State Outcome)
    (policy : Policy) : FiniteLaw State :=
  (model.transition policy).predictive model.initialState

/-- Predicted outcome marginal under a policy. -/
def predictedOutcome (model : GenerativeModel Policy State Outcome)
    (policy : Policy) : FiniteLaw Outcome :=
  model.likelihood.predictive (predictedState model policy)

/-- Exact posterior state law after a positive-mass outcome. -/
noncomputable def posteriorState
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (outcome : Outcome) (h : 0 < predictedOutcome model policy outcome) :
    FiniteLaw State :=
  model.likelihood.posterior (predictedState model policy) outcome h

/-- Surprisal of one outcome under a policy.  Positivity is required by the
downstream posterior/VFE theorems rather than hidden in this total function. -/
noncomputable def outcomeSurprisal
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (outcome : Outcome) : ℝ :=
  -Real.log (predictedOutcome model policy outcome)

/-- Posterior-form variational free energy:
`F[Q,o,π] = KL(Q || P(s|o,π)) - log P(o|π)`. -/
noncomputable def variationalFreeEnergy
    (model : GenerativeModel Policy State Outcome) (policy : Policy)
    (outcome : Outcome) (h : 0 < predictedOutcome model policy outcome)
    (recognition : FiniteLaw State) : ℝ :=
  finiteKL recognition (posteriorState model policy outcome h) +
    outcomeSurprisal model policy outcome

end FreeEnergyPrinciple
