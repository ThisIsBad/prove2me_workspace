import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_AmbientChain

namespace ProcessingNetworks.PacketNetworks

open scoped ENNReal

/-- The states reachable from `x₀` by the chain with one-step kernel `jump` (including `x₀`
itself, in zero steps): the state space `X` of Lemma 12.18's proof when `x₀ = 0`. -/
def reachableFrom {X : Type*} (jump : X → PMF X) (x₀ : X) : Set X :=
  {y | ∃ n : ℕ, 0 < stepIter jump n x₀ y}

/-- The chain is irreducible with state space `X` (Lemma 12.18's "`Z` is irreducible with state
space `𝒳`"): every state of `X` is reachable from every other state of `X` in finitely many
steps. -/
def IrreducibleOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℕ, 0 < stepIter jump n x y

/-- The chain is aperiodic on the state space `S`: every state `x ∈ S` has period `1`, i.e. the
only common divisor of the return times `{n ≥ 1 : P_x(Z(n) = x) > 0}` is `1`. -/
def AperiodicOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < stepIter jump n x x → d ∣ n) → d = 1

/-- The chain is positive recurrent on the state space `S`: every state `x ∈ S` is recurrent
with finite expected return time (mission I's `Stability.Recurrent` and `Stability.meanReturnTime`
with unit exit rates, as in mission XII's `PositiveRecurrent`, restricted to `S`). -/
def PositiveRecurrentOn {X : Type*} (jump : X → PMF X) (S : Set X) : Prop :=
  ∀ x ∈ S, Stability.Recurrent jump x ∧ Stability.meanReturnTime jump (fun _ => (1 : ℝ)) x < ⊤

end ProcessingNetworks.PacketNetworks
