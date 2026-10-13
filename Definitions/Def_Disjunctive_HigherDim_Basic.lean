import Mathlib

namespace Disjunctive.HigherDim

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `{x : x_j ∈ {0,1}}` (Balas §7.1, p. 91). -/
def ZeroOneSet {n : ℕ} (j : Fin n) : Set (Fin n → ℝ) := {x | x j = 0 ∨ x j = 1}

/-- One step of sequential convexification, `conv(S ∩ {x_j ∈ {0,1}})` (Balas §7.1, p. 91-92,
the simple description of `P_j` that Theorem 7.1 identifies with the nonlinear 3-step
construction). -/
def SplitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ (S ∩ ZeroOneSet j)

/-- `P_{i1,...,it}(K) := P_it(P_{it-1}(⋯(P_i1(K))⋯))` (Balas §7.1, p. 92): iterating
`SplitConvexify` over an explicit sequence of coordinates, applied left to right. -/
def IteratedSplit {n : ℕ} (K : Set (Fin n → ℝ)) (l : List (Fin n)) : Set (Fin n → ℝ) :=
  l.foldl SplitConvexify K

/-- `K₀ := K ∩ {x_j ∈ {0,1}, j ∈ N'}` (Balas §7.1, p. 91), the mixed 0-1 program's feasible set,
for `N'` the 0-1 index set. -/
def K0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j

/-- `M_j(K)`, the lifted polyhedron from multiplying `Ãx ≥ b̃` by `(1-x_j)` and `x_j` and
linearizing `y_i := x_i x_j` (`i ≠ j`), `x_j := x_j²` (Balas §7.1, p. 91-92, eq. (7.1)-(7.2)):
pairs `(x,y)` with `y_j = x_j` and the two linearized inequality families. -/
def Mj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ i, 0 ≤ (A.mulVec p.1) i - (A.mulVec p.2) i + b i * (p.1 j - 1)) ∧
        (∀ i, 0 ≤ (A.mulVec p.2) i - b i * p.1 j) ∧ p.2 j = p.1 j}

/-- `P_j(K)`, the projection of `M_j(K)` onto the `x`-space (Balas §7.1, p. 91-92, Step 3). -/
def Pj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) : Set (Fin n → ℝ) :=
  {x | ∃ y, (x, y) ∈ Mj A b j}

end Disjunctive.HigherDim
