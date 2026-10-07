import Mathlib

namespace Gomory69.MasterFaces

/-- Equation (5): a nonnegative integer vector on `N` represents `g₀`. -/
def GroupSolution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) (t : N → ℕ) : Prop :=
  (∑ g : N, (t g) • (g : G)) = g₀

/-- The real point corresponding to an integer solution. -/
def castSolution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {N : Finset G} (t : N → ℕ) : N → ℝ := fun g => (t g : ℝ)

/-- The solution set `T` of equation (5). -/
def solutionSet {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) : Set (N → ℕ) :=
  {t | GroupSolution N g₀ t}

/-- `P(𝒢, N, g₀)` is the real convex hull of the nonnegative integer solutions. -/
def groupPolyhedron {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) : Set (N → ℝ) :=
  convexHull ℝ (castSolution '' solutionSet N g₀)

/-- Evaluation of a normal vector on a real point of `N`-space. -/
def dot {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {N : Finset G} (π x : N → ℝ) : ℝ :=
  ∑ g : N, π g * x g

/-- A path is represented by its multiplicity vector. It is shortest to `h` when
no other nonnegative integer vector representing `h` has smaller `π`-length. -/
def IsShortest {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (h : G) (π : N → ℝ) (t : N → ℕ) : Prop :=
  GroupSolution N h t ∧
  ∀ s : N → ℕ, GroupSolution N h s →
    dot π (castSolution t) ≤ dot π (castSolution s)

/-- The tight integer points for a proposed facet inequality. -/
def tightSolutions {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) (π : N → ℝ) (π₀ : ℝ) : Set (N → ℝ) :=
  {x | ∃ t : N → ℕ, GroupSolution N g₀ t ∧ x = castSolution t ∧ dot π x = π₀}

/-- Gomory's "face" is a facet: all integer solutions satisfy the inequality, and
the tight integer solutions affinely generate its entire hyperplane. -/
def IsFace {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) (π : N → ℝ) (π₀ : ℝ) : Prop :=
  π ≠ 0 ∧
  (∀ t : N → ℕ, GroupSolution N g₀ t → π₀ ≤ dot π (castSolution t)) ∧
  (↑(affineSpan ℝ (tightSolutions N g₀ π π₀)) : Set (N → ℝ)) =
    {x | dot π x = π₀}

/-- The nonzero elements of the group, written `𝒢⁺` in the paper. -/
def masterSupport (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] : Finset G :=
  Finset.univ.filter (fun g => g ≠ 0)

/-- The coordinate space of the master polyhedron. -/
abbrev MasterIndex (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] :=
  ↥(masterSupport G)

/-- The master polyhedron `P(𝒢, g₀)`, for `g₀ ≠ 0`. -/
def masterPolyhedron {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (_hg₀ : g₀ ≠ 0) : Set (MasterIndex G → ℝ) :=
  groupPolyhedron (masterSupport G) g₀

/-- Extend a coefficient function on `𝒢⁺` by `π(0) = 0`. -/
def extendZero {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (π : MasterIndex G → ℝ) (g : G) : ℝ :=
  if hg : g = 0 then 0 else π ⟨g, by simp [masterSupport, hg]⟩

end Gomory69.MasterFaces
