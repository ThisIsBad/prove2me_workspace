import Mathlib

namespace MillerTuckerZemlin.Formulation

/-- An itinerary for problem (1) of Miller, Tucker, Zemlin, *Integer Programming Formulation of
Traveling Salesman Problems*, J. ACM 7(4) (1960), p. 326: the list of tours in the order they are
travelled, each tour being the list of cities visited between two stops at the base city `0`.
Cities are `Fin (n + 1)`: `0` is the base city and `1, …, n` are the paper's cities. -/
abbrev Itinerary (n : ℕ) := List (List (Fin (n + 1)))

/-- A legitimate itinerary of problem (1) (p. 326) with at most `p` cities per tour: every tour is
nonempty, avoids the base city `0` and visits at most `p` cities; no city is visited twice; and every
city `c ≠ 0` is visited. The number of returns to `0` is `I.length`. -/
def IsItinerary (n p : ℕ) (I : Itinerary n) : Prop :=
  (∀ T ∈ I, T ≠ [] ∧ (0 : Fin (n + 1)) ∉ T ∧ T.length ≤ p) ∧
  I.flatten.Nodup ∧
  ∀ c : Fin (n + 1), c ≠ 0 → c ∈ I.flatten

/-- The arcs travelled on one tour `T = [c₁, …, c_k]`: the consecutive pairs of the closed walk
`0, c₁, …, c_k, 0`. -/
def tourArcs {n : ℕ} (T : List (Fin (n + 1))) : List (Fin (n + 1) × Fin (n + 1)) :=
  (0 :: T).zip (T ++ [0])

/-- All arcs travelled along an itinerary, with multiplicity. -/
def arcs {n : ℕ} (I : Itinerary n) : List (Fin (n + 1) × Fin (n + 1)) :=
  I.flatMap tourArcs

/-- The number of times the itinerary travels directly from city `i` to city `j`
(the paper's correspondence: "the salesman proceeds from city i to city j if and only if
x_ij = 1", p. 327). -/
def arcCount {n : ℕ} (I : Itinerary n) (i j : Fin (n + 1)) : ℕ :=
  (arcs I).count (i, j)

/-- The total distance travelled along an itinerary, for the distances `d i j` of p. 326. -/
def itineraryLength {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n) : ℝ :=
  ((arcs I).map (fun a => d a.1 a.2)).sum

/-- The feasible set of problem (2) (p. 327): `x i j` (non-negative integers) and `u i` (arbitrary
reals) with
* `∑_{i = 0, i ≠ j}^n x_ij = 1` for `j = 1, …, n`,
* `∑_{j = 0, j ≠ i}^n x_ij = 1` for `i = 1, …, n`,
* `u_i − u_j + p x_ij ≤ p − 1` for `1 ≤ i ≠ j ≤ n`.
Problem (2) has no variables `x_ii`; the clause `x i i = 0` encodes their absence. `u 0` is not a
variable of (2) and is unconstrained. -/
def Feasible (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, x i i = 0) ∧
  (∀ j : Fin (n + 1), j ≠ 0 → ∑ i ∈ Finset.univ.filter (· ≠ j), x i j = 1) ∧
  (∀ i : Fin (n + 1), i ≠ 0 → ∑ j ∈ Finset.univ.filter (· ≠ i), x i j = 1) ∧
  (∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j →
    u i - u j + (p : ℝ) * (x i j : ℝ) ≤ (p : ℝ) - 1)

/-- The objective of problem (2) (p. 327): `∑∑_{0 ≤ i ≠ j ≤ n} d_ij x_ij`. -/
def objective {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (· ≠ i), d i j * (x i j : ℝ)

/-- The labelling of the converse (p. 328): `u_i = j` if city `i` is the `j`-th city visited in the
tour which includes city `i` (1-based); `0` for the base city and for a city on no tour. -/
def tourPosition {n : ℕ} (I : Itinerary n) (i : Fin (n + 1)) : ℕ :=
  if i = 0 then 0 else
    match I.find? (fun T => decide (i ∈ T)) with
    | some T => T.idxOf i + 1
    | none => 0

end MillerTuckerZemlin.Formulation
