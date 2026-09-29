import Mathlib

namespace JewellMRP.Discounted

open MeasureTheory

/-- A finite **Markov-renewal program** (Jewell 1963, pp. 940–942), for one fixed family of
one-transition discounted returns.

* `S` is the finite set of states `1, …, N` and `A` the finite set of alternatives
  `1, …, Z`; every alternative is available in every state.
* `p z i j` is the transition probability `p^z_{ij}` of (1): each `p z` is a stochastic matrix.
* `F z i j` is the law of the transition interval `τ(i, j)` under alternative `z`, i.e. the
  distribution `F^z_{ij}` of (2): a probability measure on `ℝ` giving no mass to `(-∞, 0]`
  (the interval is nonnegative and `F_{ij}(0) = 0`, p. 941).
* `ρ α z i j` is the expected discounted return `ρ^z_{ij}(α)` earned during a transition from
  `i` to `j` under alternative `z` with continuous discount factor `α`, eq. (4); here it is
  arbitrary real data. -/
structure MRP (S A : Type*) [Fintype S] where
  /-- Transition probabilities `p^z_{ij}`. -/
  p : A → S → S → ℝ
  p_nonneg : ∀ z i j, 0 ≤ p z i j
  p_sum : ∀ z i, ∑ j, p z i j = 1
  /-- Sojourn-time distributions `F^z_{ij}`. -/
  F : A → S → S → Measure ℝ
  F_prob : ∀ z i j, IsProbabilityMeasure (F z i j)
  /-- `τ ≥ 0` and `F^z_{ij}(0) = Pr{τ ≤ 0} = 0`. -/
  F_Iic_zero : ∀ z i j, F z i j (Set.Iic 0) = 0
  /-- One-transition expected discounted returns `ρ^z_{ij}(α)`. -/
  ρ : ℝ → A → S → S → ℝ

variable {S A : Type*} [Fintype S]

/-- The Laplace–Stieltjes transform (7) of the sojourn distribution:
`f̃^z_{ij}(s) = ∫_0^∞ e^{-s t} dF^z_{ij}(t)`. The integral is taken over `(0, ∞)`, which carries
all the mass of `F^z_{ij}`. -/
noncomputable def ftilde (M : MRP S A) (z : A) (i j : S) (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂(M.F z i j)

/-- The entries of the matrix `q̃(s) = [p^z_{ij} f̃^z_{ij}(s)]` (p. 945), for alternative `z`. -/
noncomputable def qtilde (M : MRP S A) (s : ℝ) (z : A) (i j : S) : ℝ :=
  M.p z i j * ftilde M z i j s

/-- The average one-step discounted return (5): `ρ^z_i(α) = Σ_j p^z_{ij} ρ^z_{ij}(α)`. -/
def rhoState (M : MRP S A) (α : ℝ) (z : A) (i : S) : ℝ :=
  ∑ j, M.p z i j * M.ρ α z i j

/-- The test quantity of Fig. 1 for alternative `z` in state `i` against returns `v`:
`ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j`. -/
noncomputable def test (M : MRP S A) (α : ℝ) (z : A) (i : S) (v : S → ℝ) : ℝ :=
  rhoState M α z i + ∑ j, qtilde M α z i j * v j

/-- The maximal test quantity `max_z [ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j]` of (6), (14)
and Fig. 1. -/
noncomputable def maxTest [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (v : S → ℝ) (i : S) :
    ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun z => test M α z i v)

end JewellMRP.Discounted
