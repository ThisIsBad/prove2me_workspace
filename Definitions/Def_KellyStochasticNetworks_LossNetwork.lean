import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

/-- The state space `S(C) = {n : A n ≤ C}` of a loss network with fixed routing: `n r` calls are
in progress on route `r`, route `r` requires `A j r` circuits from link `j`, and link `j` has
`C j` circuits.  Kelly–Yudovina, *Stochastic Networks*, pp. 50 and 53. -/
def lossStates {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ) : Set (Fin R → ℕ) :=
  {n | ∀ j, (∑ r, A j r * n r) ≤ C j}

/-- The unnormalized product-form weight `∏_r ν_r^{n_r} / n_r!` of equation (3.3). -/
noncomputable def lossWeight {R : ℕ} (ν : Fin R → ℝ) (n : Fin R → ℕ) : ℝ :=
  ∏ r, ν r ^ n r / (Nat.factorial (n r) : ℝ)

/-- A Markov process truncated to a subset `A` of its state space: the rates are unchanged
between states of `A`, and a transition leaving `A` is suppressed.  Kelly–Yudovina, p. 52. -/
def truncatedRates {S : Type*} (q : S → S → ℝ) (A : Set S) : A → A → ℝ :=
  fun j k => q (j : S) (k : S)

/-- The objective of the **Dual** problem (3.5) of section 3.4. -/
noncomputable def dualObjective {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (y : Fin J → ℝ) : ℝ :=
  (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) + ∑ j, y j * (C j : ℝ)

/-- The **Erlang fixed point equations** (3.7):
`E_j = E((1 - E_j)⁻¹ ∑_r A_{jr} ν_r ∏_i (1 - E_i)^{A_{ir}}, C_j)` for every link `j`. -/
def ErlangFixedPoint {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (E : Fin J → ℝ) : Prop :=
  ∀ j, E j = erlang ((1 - E j)⁻¹ * ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r)) (C j)

end KellyStochasticNetworks
