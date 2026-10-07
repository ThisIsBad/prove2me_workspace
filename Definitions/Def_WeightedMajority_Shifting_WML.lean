import Mathlib

namespace WeightedMajority.Shifting

open Finset

/-- Total weight `Σ_j w_j` of a weight vector on a pool of `n` algorithms. -/
noncomputable def totalWeight {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j

/-- `voteWeight w x b` is the total weight `q_b` of the pool members whose prediction in the
current trial (`x i`) equals `b`. -/
noncomputable def voteWeight {n : ℕ} (w : Fin n → ℝ) (x : Fin n → Bool) (b : Bool) : ℝ :=
  ∑ i ∈ univ.filter (fun i => x i = b), w i

/-- The weighted-majority prediction rule (p. 215): predict according to the larger of
`q_0 = voteWeight w x false` and `q_1 = voteWeight w x true`; in case of a tie either
prediction is allowed. -/
def IsMajorityPrediction {n : ℕ} (w : Fin n → ℝ) (x : Fin n → Bool) (lam : Bool) : Prop :=
  (voteWeight w x true < voteWeight w x false → lam = false) ∧
  (voteWeight w x false < voteWeight w x true → lam = true)

/-- The WML weight update of one trial (p. 223). If the master's prediction `lam` differs from
the label `ρ`, every pool member `i` whose prediction `x i` disagrees with the label has its
weight multiplied by `β`, but only if its weight before the update is strictly larger than
`γ / n` times the total weight at the beginning of the trial. All other weights, and all weights
in a trial where the master is right, are unchanged. -/
noncomputable def wmlUpdate {n : ℕ} (β γ : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) (ρ lam : Bool) :
    Fin n → ℝ :=
  fun i => if lam ≠ ρ ∧ x i ≠ ρ ∧ (γ / (n : ℝ)) * totalWeight w < w i then β * w i else w i

/-- A run of WML (p. 223) with parameters `β, γ` on `T` trials, pool `Fin n`, pool predictions
`x t i`, labels `ρ t`, weights `w t` at the beginning of trial `t` (`w 0` the initial weights,
`w T` the final weights) and master predictions `lam t`. The initial weights are positive, each
prediction is a weighted majority vote (ties arbitrary), and the weights evolve by `wmlUpdate`. -/
structure IsWMLRun {n T : ℕ} (β γ : ℝ) (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool) : Prop where
  init_pos : ∀ i, 0 < w 0 i
  predict : ∀ t : Fin T, IsMajorityPrediction (w t) (x t) (lam t)
  update : ∀ t : Fin T, w ((t : ℕ) + 1) = wmlUpdate β γ (w t) (x t) (ρ t) (lam t)

/-- Number of mistakes of the master: trials `t` with `lam t ≠ ρ t`. -/
def masterMistakes {T : ℕ} (ρ lam : Fin T → Bool) : ℕ :=
  (univ.filter (fun t : Fin T => lam t ≠ ρ t)).card

/-- Number of mistakes of pool member `i` on the trials `t` with `a ≤ t < b`. -/
def memberMistakesOn {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (a b : ℕ)
    (i : Fin n) : ℕ :=
  (univ.filter (fun t : Fin T => a ≤ (t : ℕ) ∧ (t : ℕ) < b ∧ x t i ≠ ρ t)).card

/-- Minimum, over the pool, of the number of mistakes on the trials `a ≤ t < b`
(`m_0` of Lemma 3.1, `m_i` of Theorem 3.1). The infimum is over the finite set `Fin n`; it is a
minimum when `n > 0`. -/
noncomputable def bestMistakesOn {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool)
    (a b : ℕ) : ℕ :=
  ⨅ i : Fin n, memberMistakesOn x ρ a b i

/-- The contraction factor `u = (1 + β)/2 + (1 − β)γ` of Lemma 3.1. -/
noncomputable def uFactor (β γ : ℝ) : ℝ :=
  (1 + β) / 2 + (1 - β) * γ

end WeightedMajority.Shifting
