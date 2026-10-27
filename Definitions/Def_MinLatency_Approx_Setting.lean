import Mathlib

namespace MinLatency.Approx

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §1, p. 1 and §3.2, p. 6: a finite metric on the point set `V`: symmetric, zero on the diagonal,
positive between distinct points (§3.2 works in "metric spaces"), and satisfying the triangle
inequality. -/
structure IsMetric (d : V → V → ℝ) : Prop where
  symm : ∀ u v, d u v = d v u
  self : ∀ u, d u u = 0
  pos : ∀ u v, u ≠ v → 0 < d u v
  triangle : ∀ u v w, d u w ≤ d u v + d v w

/-- Length of a walk (a list of points): the sum of the distances between consecutive points.
A walk with fewer than two points has length `0`. -/
def pathLen (d : V → V → ℝ) : List V → ℝ
  | u :: v :: t => d u v + pathLen d (v :: t)
  | _ => 0

/-- Closed length of a tour: its path length plus the return leg from its last point to its first
point. The empty list has closed length `0`. -/
def tourLen (d : V → V → ℝ) : List V → ℝ
  | [] => 0
  | u :: t => pathLen d (u :: t) + d ((u :: t).getLast (List.cons_ne_nil u t)) u

/-- A tour rooted at `p` (p. 6): a list without repetitions whose first point is `p`; it is closed
by the return leg to `p` (see `tourLen`). -/
def IsRootedTour (p : V) (T : List V) : Prop := T.head? = some p ∧ T.Nodup

/-- The number of points of `V` that the list `T` does not visit. -/
def missed (T : List V) : ℕ := (Finset.univ.filter (fun v => v ∉ T)).card

/-- p. 6: the prize-collecting cost of a tour `T` under the penalty vector `π`: the total distance
travelled (closed length) plus the sum of the penalties of the points not visited. -/
def pcCost (d : V → V → ℝ) (π : V → ℝ) (T : List V) : ℝ :=
  tourLen d T + ∑ v ∈ Finset.univ.filter (fun v => v ∉ T), π v

/-- Lemma 3, p. 6, as used in the proof of Corollary 4 ("a 2-approximation algorithm for the
prize-collecting traveling salesman problem"): the oracle `O` maps every nonnegative penalty vector
to a tour rooted at `p` whose prize-collecting cost is at most twice that of every tour rooted
at `p`. -/
def PCAdmissible (d : V → V → ℝ) (p : V) (O : (V → ℝ) → List V) : Prop :=
  ∀ π : V → ℝ, (∀ v, 0 ≤ π v) →
    IsRootedTour p (O π) ∧ ∀ T, IsRootedTour p T → pcCost d π (O π) ≤ 2 * pcCost d π T

/-- The latency of `v` in the walk `W` (abstract, §1): the length of `W` up to the **first**
occurrence of `v`. -/
def firstVisit (d : V → V → ℝ) (W : List V) (v : V) : ℝ :=
  pathLen d (W.take (W.idxOf v + 1))

/-- The total latency of the walk `W`: the sum over all points of their latencies. -/
def walkLatency (d : V → V → ℝ) (W : List V) : ℝ := ∑ v, firstVisit d W v

/-- A walk starting at `p` that visits every point (§1, p. 1–3: the MLT may revisit points). -/
def IsCoveringWalk (p : V) (W : List V) : Prop := W.head? = some p ∧ ∀ v, v ∈ W

/-- Definition and Comment, p. 6, in the form called with the bound `L` only: `A` is an
`(α, β)`-TSP-approximator for the instance `(d, p)` if, for every positive bound `L` and every `k`,
whenever some tour rooted at `p` of closed length at most `L` misses at most `k` points, `A L` is a
tour rooted at `p` of closed length at most `β L` missing at most `α k` points. -/
def IsTSPApprox (d : V → V → ℝ) (p : V) (α β : ℝ) (A : ℝ → List V) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ k : ℕ, (∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) →
    IsRootedTour p (A L) ∧ tourLen d (A L) ≤ β * L ∧ (missed (A L) : ℝ) ≤ α * k

/-- Proof of Corollary 4, p. 6: the penalty placed on each point when the comparison tour of length
`L` misses `k` points: `P = 2L/k` (the page's `2L/(εn)` with `εn = k`) for `k ≥ 1`, and `P = 4L`
for `k = 0`. -/
noncomputable def penalty (L : ℝ) (k : ℕ) : ℝ := if k = 0 then 4 * L else 2 * L / k

/-- Proof of Corollary 4, p. 6: the `(3, 6)`-TSP-approximator built from the prize-collecting
oracle `O`, for the bound `L`. Call `O` with the constant penalty `penalty L k` for every
`k = 0, …, |V| - 1`; among the returned tours of closed length at most `6L`, return one visiting the
most points (the first such in the order of `k`); if there is none, return `[p]`. -/
noncomputable def cor4Approx (d : V → V → ℝ) (p : V) (O : (V → ℝ) → List V) (L : ℝ) : List V := by
  classical
  exact
    match (((List.range (Fintype.card V)).map (fun k => O (fun _ => penalty L k))).filter
        (fun T => decide (tourLen d T ≤ 6 * L))).argmax (fun T => T.toFinset.card) with
    | some T => T
    | none => [p]

/-- Proof of Lemma 5, p. 6: the distance `δ` from the starting point `p` to its nearest neighbour;
`1` if `p` is the only point. -/
noncomputable def nnDist (d : V → V → ℝ) (p : V) : ℝ :=
  if h : (Finset.univ.filter (fun v => v ≠ p)).Nonempty then
    (Finset.univ.filter (fun v => v ≠ p)).inf' h (fun v => d p v)
  else 1

/-- Proof of Lemma 5, p. 6: the bound of round trip `j = 0, 1, 2, …`, namely `2^{j+1} δ` (the page's
`L = 2, 4, 8, …` with `δ` normalised to `1`). -/
noncomputable def budget (d : V → V → ℝ) (p : V) (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1) * nnDist d p

/-- Proof of Lemma 5, p. 6: the concatenation `T_0 ++ T_1 ++ ⋯ ++ T_J` of the round trips
`T_j = A (2^{j+1} δ)`. -/
noncomputable def doublingWalk (d : V → V → ℝ) (p : V) (A : ℝ → List V) (J : ℕ) : List V :=
  (List.range (J + 1)).flatMap (fun j => A (budget d p j))

/-- The run stops after round trip `J`: round trip `J` visits every point and no earlier round trip
does. -/
def StopsAt (d : V → V → ℝ) (p : V) (A : ℝ → List V) (J : ℕ) : Prop :=
  (∀ v, v ∈ A (budget d p J)) ∧ ∀ j < J, ¬ ∀ v, v ∈ A (budget d p j)

/-- The bit size of a rational `a/b` in lowest terms: `1 + ⌈log₂(|a|+1)⌉ + ⌈log₂(b+1)⌉`
(`Nat.size k = ⌈log₂(k+1)⌉`). -/
def ratSize (r : ℚ) : ℕ := 1 + Nat.size r.num.natAbs + Nat.size r.den

/-- The bit size of a rational distance matrix: the sum of the sizes of its entries. -/
def instSize (d : V → V → ℚ) : ℕ := ∑ u, ∑ v, ratSize (d u v)

end MinLatency.Approx
