import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mcmc

namespace LogSobolevMC.Metropolis

noncomputable section

open scoped BigOperators

/-- The binomial distribution `π(x) = 2⁻ⁿ C(n, x)` on `{0, 1, …, n}` = `Fin (n + 1)`
(Example 1.1, p. 698). -/
def binomPi (n : ℕ) : Fin (n + 1) → ℝ :=
  fun x => ((n.choose (x : ℕ) : ℕ) : ℝ) / 2 ^ n

/-- The base chain of Example 1.1 (p. 698), nearest-neighbour random walk on
`{0, 1, …, n}` = `Fin (n + 1)`, held at the ends:
`K(x, x + 1) = K(x, x − 1) = 1/2` for `1 ≤ x ≤ n − 1`, and
`K(0, 1) = K(0, 0) = K(n, n − 1) = K(n, n) = 1/2`; all other entries are `0`. -/
def baseWalk (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun x y =>
    if (y : ℕ) = (x : ℕ) + 1 ∨ (y : ℕ) + 1 = (x : ℕ) then 1 / 2
    else if x = y ∧ ((x : ℕ) = 0 ∨ (x : ℕ) = n) then 1 / 2
    else 0

/-- The Metropolis chain `M` of Example 1.1, (1.9), p. 698: the standard Metropolis
construction (`MarkovMixing.metropolis`: a proposal `x → y ≠ x` of the base chain is
accepted with probability `min(1, π(y)/π(x))`, the rejected mass stays at `x`) applied
to `baseWalk n` and the binomial distribution `binomPi n`. -/
def binomMetropolis (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  MarkovMixing.metropolis (baseWalk n) (binomPi n)

/-- The two-point chain of Example 3.1 (p. 715) on `{−1, 1}`, encoded as `Fin 2`
(`0 ↦ −1`, `1 ↦ 1`): `K(−1, 1) = K(1, −1) = 1`, `K(−1, −1) = K(1, 1) = 0`. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => if a = b then 0 else 1

/-- The hypercube chain of Example 3.2 (p. 717) on `{−1, 1}ⁿ` = `Fin n → Fin 2`:
`K(x, y) = 1/n` if `x, y` differ at exactly one coordinate, and `0` otherwise. -/
def hypercube (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ :=
  fun x y => if (Finset.univ.filter fun i => x i ≠ y i).card = 1 then 1 / (n : ℝ) else 0

/-- The number of coordinates of `x ∈ {−1, 1}ⁿ` equal to `1` (encoded as `(1 : Fin 2)`),
as an element of `{0, 1, …, n}` = `Fin (n + 1)` (Example 3.3, pp. 718–719). -/
def ones (n : ℕ) (x : Fin n → Fin 2) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => x i = 1).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- The Ehrenfest chain of Example 3.3 (p. 719) on `{0, 1, …, n}` = `Fin (n + 1)`:
`P(x, x + 1) = (n − x)/n` for `0 ≤ x ≤ n − 1`, `P(x, x − 1) = x/n` for `1 ≤ x ≤ n`,
and `P(x, y) = 0` otherwise. -/
def ehrenfest (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun x y =>
    if (y : ℕ) = (x : ℕ) + 1 then ((n : ℝ) - ((x : ℕ) : ℝ)) / n
    else if (y : ℕ) + 1 = (x : ℕ) then ((x : ℕ) : ℝ) / n
    else 0

end

end LogSobolevMC.Metropolis
