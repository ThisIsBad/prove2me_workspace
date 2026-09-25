import Mathlib

namespace KellyStochasticNetworks

/-- **Detailed balance.** A collection of numbers `π` and a matrix of transition rates `q`
on a state space `S` satisfy detailed balance when `π j * q j k = π k * q k j` for all
states `j, k`.  This is equation (1.4) of Kelly–Yudovina, *Stochastic Networks*. -/
def DetailedBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j k : S, π j * q j k = π k * q k j

/-- **The equilibrium (full balance) equations.** `π` satisfies the equilibrium equations for
the transition rates `q` when `π j * ∑ k, q j k = ∑ k, π k * q k j` for every state `j`.
This is equation (1.2) of Kelly–Yudovina, *Stochastic Networks*; the sums range over the whole
(countable) state space, so they are written as unconditional sums. -/
def FullBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j : S, π j * (∑' k : S, q j k) = ∑' k : S, π k * q k j

/-- **The transition rates of the time-reversed process**, `q' j k = π k * q k j / π j`,
as computed in Proposition 1.1 of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def reversedRates {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : S → S → ℝ :=
  fun j k => π k * q k j / π j

end KellyStochasticNetworks
