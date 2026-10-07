import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

/-- The two standing assumptions Balinski places on the system (1) `AX ≤ b` (p. 432), with
the rows of `A` given as vectors `a i ∈ ℝⁿ`, `i < m`:
(i) the only solution of `AX ≤ 0` is `X = 0`;
(ii) some `X⁰` satisfies `AX⁰ < b`, i.e. every inequality strictly. -/
structure StandingAssumptions {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : Fin m → ℝ) : Prop where
  only_zero : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, ⟪a i, x⟫ ≤ 0) → x = 0
  strict_point : ∃ x₀ : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, x₀⟫ < b i

/-- The graph `G(S)` of a set `S` (p. 432): its points are the vertices (extreme points) of `S`,
and two vertices `u ≠ v` are joined by a line when the segment `[u, v]` is an edge of `S`,
i.e. an extreme subset of `S` (`Hirsch.Adj`). -/
def polyGraph {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) :
    SimpleGraph (Set.extremePoints ℝ S) where
  Adj u v := Hirsch.Adj S u v
  symm := ⟨fun u v (h : Hirsch.Adj S u v) =>
    ⟨fun e => h.1 e.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun u (h : Hirsch.Adj S u u) => h.1 rfl⟩

end Balinski61.Connectivity
