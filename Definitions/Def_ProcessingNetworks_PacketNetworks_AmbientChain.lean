import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.PacketNetworks

open scoped ENNReal

/-- `n`-step transition probabilities of a discrete-time Markov chain with one-step kernel
`jump : X → PMF X` (mission I's `Stability.stepIter`; drafts in this series import mission I's
definitions and nothing else). -/
noncomputable abbrev stepIter {X : Type*} (jump : X → PMF X) : ℕ → X → PMF X :=
  Stability.stepIter jump

/-- The chain with one-step kernel `jump` is irreducible: every state is reachable from every
other state in finitely many steps (mission I's `Stability.Irreducible`). -/
abbrev Irreducible {X : Type*} (jump : X → PMF X) : Prop :=
  Stability.Irreducible jump

/-- Positive recurrence of a *discrete-time* Markov chain `Z = {Z(τ), τ ∈ Z+}` with one-step
kernel `jump` (the notion Definition 12.3 invokes for the DTMC `Z`): every state `x` is recurrent
(the chain started at `x` returns to `x` with probability one) and the expected return time
`E_x(T_x) = ∑ₙ P_x(T_x > n)` is finite. This is mission I's continuous-time
`Stability.PositiveRecurrent jump rate` (Definition D.15) with unit exit rates, under which the
continuous-time chain built from `jump` holds one unit-mean exponential clock per step, so
`E_x(T_x)` is the expected number of steps of the discrete-time chain before it returns to `x`.
Recurrence is part of the definition: finiteness of `∑ₙ n · f_n(x)` alone is satisfied by every
transient state, since its first-return probabilities `f_n(x)` sum to less than one. -/
def PositiveRecurrent {X : Type*} (jump : X → PMF X) : Prop :=
  Stability.PositiveRecurrent jump (fun _ => (1 : ℝ))

end ProcessingNetworks.PacketNetworks
