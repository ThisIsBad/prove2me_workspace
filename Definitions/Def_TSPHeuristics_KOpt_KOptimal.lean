import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.KOpt

/-- The edge set of the tour `τ 0, τ 1, …, τ (n - 1), τ 0`, as unordered pairs. -/
def tourEdges {n : ℕ} (τ : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun i => s(τ i, τ (finRotate n i)))

/-- The edge set of the closed tour through the list `T` in list order (the last entry is joined
to the first), as unordered pairs. -/
def listEdges {n : ℕ} (T : List (Fin n)) : Finset (Sym2 (Fin n)) :=
  (List.zipWith (fun x y => s(x, y)) T (T.rotate 1)).toFinset

/-- k-optimality (p. 579): "Define a k-change of a tour as the deletion of k edges and their
replacement by k other edges so that another tour is obtained. Define a tour as k-optimal (Lin
[10]) if no k-change produces a better tour." The tour is given as the list `T` (in list order,
closed up). A k-change of `T` produces exactly a tour `τ` whose edge set misses exactly `k` of the
edges of `T`; `T` is k-optimal if no such `τ` is strictly shorter. Every tour at edge difference
`k` is compared, not only special moves such as segment reversals. -/
def IsKOptimal {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (T : List (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), (listEdges T \ tourEdges τ).card = k →
    TSPHeuristics.Shared.cycleLength d T ≤ TSPHeuristics.Shared.tourLength d τ

/-- k-optimality (p. 579) of the tour given by the permutation `τ`: no tour `σ` whose edge set
misses exactly `k` of the edges of `τ` is strictly shorter than `τ`. -/
def IsKOptimalTour {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), (tourEdges τ \ tourEdges σ).card = k →
    TSPHeuristics.Shared.tourLength d τ ≤ TSPHeuristics.Shared.tourLength d σ

end TSPHeuristics.KOpt
