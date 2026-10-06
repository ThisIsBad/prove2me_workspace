import Mathlib

namespace BregmanRelax.EqConstr

/-- The function (1.4) of Bregman (1967, p. 206) built from `f` and its gradient map `g`:
`D(x, y) = f(x) - f(y) - (g(y), x - y)`. -/
noncomputable def bregmanD {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  f x - f y - inner ℝ (g y) (x - y)

/-- The hyperplane `A_i = {x ∈ E^p | (A_i, x) = b_i}` of the `i`-th equation of `Ax = b`
(Theorem 3, p. 209); the row `A_i` of the matrix `A` is the vector `a i`. -/
def hyperplane {p m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ) (i : Fin m) :
    Set (EuclideanSpace ℝ (Fin p)) :=
  {x | inner ℝ (a i) x = b i}

/-- The feasible set `R = {x ∈ E^p | Ax = b, x ∈ S̄}` of problem (2.1)–(2.3) (p. 208). -/
def feasibleEq {p m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin p))) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | ∀ i, inner ℝ (a i) x = b i} ∩ closure S

/-- The set `Z` of p. 209: the points `x ∈ S` at which the gradient is a combination
`g(x) = uA = ∑ i, u i • a i` of the rows of `A`, for some `u ∈ E^m`. -/
def Zset {p m : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | x ∈ S ∧ ∃ u : Fin m → ℝ, g x = ∑ i, u i • a i}

/-- Condition (2) of Note 1 (p. 204), with the limit `y*` taken in the closure `S̄`:
if `y n ∈ S` and `y n → y* ∈ S̄`, then `D(y*, y n) → 0`. -/
def Cond2 {p : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (D : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  ∀ (y : ℕ → EuclideanSpace ℝ (Fin p)) (y' : EuclideanSpace ℝ (Fin p)), (∀ n, y n ∈ S) →
    y' ∈ closure S → Filter.Tendsto y Filter.atTop (nhds y') →
    Filter.Tendsto (fun n => D y' (y n)) Filter.atTop (nhds 0)

end BregmanRelax.EqConstr
