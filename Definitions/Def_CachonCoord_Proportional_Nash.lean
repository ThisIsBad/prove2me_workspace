import Mathlib

namespace CachonCoord.Proportional

/-- Pure-strategy Nash equilibrium of an `n`-player game in which every player chooses a
nonnegative real number (an order quantity) and `payoff i q` is player `i`'s payoff at the
strategy profile `q`. The profile `q` is a Nash equilibrium if every coordinate is feasible
(`q i ≥ 0`) and no player gains by a unilateral deviation to any other feasible `x ≥ 0`
(Cachon 2003, 3rd draft, §6.5.1, p. 50: "each retailer's order quantity is a best response"). -/
def IsNash {n : ℕ} (payoff : Fin n → (Fin n → ℝ) → ℝ) (q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧
    ∀ (i : Fin n) (x : ℝ), 0 ≤ x → payoff i (Function.update q i x) ≤ payoff i q

end CachonCoord.Proportional
