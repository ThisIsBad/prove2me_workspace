import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

namespace SecretaryWD.DiscUpper

/-- The number of discount classes the algorithm draws from, `M = 3⌈log₂ n⌉ + 2`. -/
def classCount (n : ℕ) : ℕ := 3 * Nat.clog 2 n + 2

/-- The payoff of `A_c` on order `π`: run the classical secretary rule on the arrivals at the
times of `P_c` only, in time order (the `k`-th time of `P_c` is `(P_c).orderEmbOfFin rfl k`),
comparing them by the tie-break key of the arriving element; if it selects the arrival at time
`i`, earn `d(i) · v(π(i))`, otherwise `0`. -/
noncomputable def classPayoff {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) (π : Equiv.Perm (Fin n)) : ℝ :=
  match classicalSecretary (discountClass d c).card
      (fun k => tieKey v (π ((discountClass d c).orderEmbOfFin rfl k))) with
  | none => 0
  | some k =>
      d ((discountClass d c).orderEmbOfFin rfl k) *
        v (π ((discountClass d c).orderEmbOfFin rfl k))

/-- `E_π[A_c]`, the expected payoff of `A_c`. -/
noncomputable def classValue {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) : ℝ :=
  uniformAvg fun π => classPayoff d v c π

/-- `E[A]` for the algorithm of Theorem 4.4: `c` uniform on `{1, …, M}`, then `A_c`. -/
noncomputable def algorithmValue {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  (1 / (classCount n : ℝ)) * ∑ c ∈ Finset.Icc 1 (classCount n), classValue d v c

end SecretaryWD.DiscUpper
