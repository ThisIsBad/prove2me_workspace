import Mathlib

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, § 3, Eq. (3.3), p. 285 and § 11, Eq. (11.1), p. 294:
the statement "`Max_x Min_y K(x, y) = Min_y Max_x K(x, y)`, and the common value is `v`", with
every maximum and minimum attained.

* The first clause says that for some `x ∈ X` the minimum of `y ↦ K(x, y)` over `Y` is attained
  and equals `v`, and that no `x ∈ X` has an attained minimum above `v`: `v = Max_x Min_y K`.
* The second clause says the same for `Min_y Max_x K`.

Nothing is assumed about `K`, `X`, `Y`: the predicate asserts attainment rather than relying on
`sSup`/`sInf` of possibly empty or unbounded sets. -/
def IsMaxMinMinMaxValue {α β : Type*} (K : α → β → ℝ) (X : Set α) (Y : Set β) (v : ℝ) :
    Prop :=
  IsGreatest {w | ∃ x ∈ X, IsLeast ((fun y => K x y) '' Y) w} v ∧
    IsLeast {w | ∃ y ∈ Y, IsGreatest ((fun x => K x y) '' X) w} v

/-- Ch. X, § 2, Eqs. (2.2)–(2.3), p. 285: the bilinear form `Σ_{i,j} a_ij p_i q_j` of a matrix
`A = (a_ij)` evaluated at the vectors `p` and `q` (the expected return when the players use the
distribution vectors `p`, `q`). -/
def bilin {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (p : ι → ℝ) (q : κ → ℝ) :
    ℝ :=
  ∑ i, ∑ j, A i j * p i * q j

/-- The bilinear form of Ch. X, Theorem 5, Eq. (19.1), p. 303, at the integer `x`:
`p₁q₁ f(x − 1) + p₁q₂ f(x + a) + p₂q₁ f(x + c) + p₂q₂ f(x − b)`, with `p = (p₁, p₂)` indexed by
`Fin 2` (`p 0 = p₁`, `p 1 = p₂`), and likewise `q`. -/
def survivalPayoff (a b c : ℤ) (f : ℤ → ℝ) (x : ℤ) (p q : Fin 2 → ℝ) : ℝ :=
  p 0 * q 0 * f (x - 1) + p 0 * q 1 * f (x + a) + p 1 * q 0 * f (x + c) + p 1 * q 1 * f (x - b)

end BellmanDP.Games
