import Mathlib

namespace KellyStochasticNetworks

/-- **Erlang's formula.** For a traffic intensity `ν` and `C` circuits,
`E(ν, C) = (ν ^ C / C !) / ∑ j ≤ C, ν ^ j / j !`.
This is equation (1.5) of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def erlang (ν : ℝ) (C : ℕ) : ℝ :=
  (ν ^ C / (Nat.factorial C : ℝ)) /
    ∑ j ∈ Finset.range (C + 1), ν ^ j / (Nat.factorial j : ℝ)

/-- **The transition rates of the Erlang loss link** with `C` parallel circuits, calls arriving
as a Poisson process of rate `lam` and call holding times exponential of parameter `mu`.
The state is the number of busy circuits, so `q j (j+1) = lam` for `j < C`,
`q j (j-1) = j * mu` for `j ≥ 1`, and every other rate — including `q j j` — is zero.
These are the rates displayed on p. 18 of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def erlangRates (lam mu : ℝ) (C : ℕ) : Fin (C + 1) → Fin (C + 1) → ℝ :=
  fun j k =>
    if (k : ℕ) = (j : ℕ) + 1 then lam
    else if (j : ℕ) = (k : ℕ) + 1 then ((j : ℕ) : ℝ) * mu
    else 0

end KellyStochasticNetworks
