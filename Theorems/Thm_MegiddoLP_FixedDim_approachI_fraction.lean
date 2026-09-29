import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

/-!
Megiddo, J. ACM 31 (1984), §3.2 pp. 118 and 121 (Approach I): `A(d) = 2^{d-1}` queries
suffice to determine the position of `x*` relative to at least `B(d)·n` of `n` given
hyperplanes in `ℝ^d`, where `B(d) = 2^{1-2^d}`. The count `B(d)·n` is read as
`⌊n / 2^{2^d - 1}⌋`.
-/

namespace MegiddoLP.FixedDim

/-- **Approach I: `A(d) = 2^{d-1}`, `B(d) = 2^{1-2^d}`.** For `d ≥ 1` and `n` hyperplanes
`{aᵢ ⬝ᵥ x = bᵢ}` in `ℝ^d` with `aᵢ ≠ 0`, there is a strategy which, for every unknown point `x`,
makes at most `2^{d-1}` queries and reports correct positions for at least
`⌊n / 2^{2^d - 1}⌋` of the hyperplanes. -/
theorem approachI_fraction (d n : ℕ) (hd : 1 ≤ d) (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree d (Fin n → Option Ordering), ∀ x : Fin d → ℝ,
      T.numQueries x ≤ 2 ^ (d - 1) ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n / 2 ^ (2 ^ d - 1) ≤ (Finset.univ.filter fun i => (T.eval x i).isSome).card := by sorry

end MegiddoLP.FixedDim
