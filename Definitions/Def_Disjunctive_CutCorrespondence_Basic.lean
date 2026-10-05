import Mathlib

namespace Disjunctive.CutCorrespondence

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `{x : x_j ∈ {0,1}}` (restated locally). -/
def ZeroOneSet {n : ℕ} (j : Fin n) : Set (Fin n → ℝ) := {x | x j = 0 ∨ x j = 1}

/-- One step of sequential convexification, `conv(S ∩ {x_j ∈ {0,1}})` (restated locally; this is
the unstrengthened lift-and-project cut closure for disjunction `j`, by Theorem 7.1). -/
def SplitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ (S ∩ ZeroOneSet j)

/-- `IteratedSplit K l := SplitConvexify` folded left to right over `l` (restated locally). -/
def IteratedSplit {n : ℕ} (K : Set (Fin n → ℝ)) (l : List (Fin n)) : Set (Fin n → ℝ) :=
  l.foldl SplitConvexify K

/-- `K₀ := K ∩ {x_j ∈ {0,1}, j ∈ N'}` (restated locally). -/
def K0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j

end Disjunctive.CutCorrespondence
