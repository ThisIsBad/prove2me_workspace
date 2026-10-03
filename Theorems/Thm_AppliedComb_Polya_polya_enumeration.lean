import Mathlib
import Definitions.Def_AppliedComb_Polya_cycleIndex
import Definitions.Def_AppliedComb_Polya_patternInventory

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Theorem 15.11 (Pólya's Enumeration Theorem), p. 302. Let `S` be a set with
`|S| = r` and `𝒞` the set of colorings of `S` using the colors `c_1, …, c_m`. If a permutation
group `G` acts on `S` to induce an equivalence relation on `𝒞`, then
`P_G(∑ c_i, ∑ c_i^2, …, ∑ c_i^r)` is the generating function for the number of nonequivalent
colorings of `S` in `𝒞`: substituting the power sum `∑_{i=1}^m c_i^k` for `x_k` (`1 ≤ k ≤ r`)
in the cycle index `P_G` gives the pattern inventory. The variable `X k` (`k : Fin r`) of `P_G`
stands for `x_{k+1}`, and the variable `X i` (`i : Fin m`) for the color `c_{i+1}`. -/
theorem polya_enumeration {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) (m : ℕ) :
    bind₁ (fun k : Fin (Fintype.card S) => ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k.val + 1))
        (cycleIndex G) = patternInventory G m := by sorry

end AppliedComb.Polya

