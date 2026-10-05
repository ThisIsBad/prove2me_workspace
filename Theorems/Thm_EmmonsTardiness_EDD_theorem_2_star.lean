import Mathlib
import Definitions.Def_EmmonsTardiness_EDD_Model

namespace EmmonsTardiness.EDD

/-- Emmons 1969, p. 713, Theorem 2*: for any two jobs `J_j`, `J_k` with `j < k`, if
(1) `k ← A_k`, (2) `d_j > d_k`, and (3) `d_j + p_j ≥ Σ_{A_k′} p_i` with `A_k′ = J \ A_k`,
then `k ← j`. Hypothesis (1) and the conclusion are read existentially over optimal schedules:
if some optimal schedule has `J_k` before every job of `A_k`, then some optimal schedule has
`J_k` before every job of `A_k` and before `J_j`. -/
theorem theorem_2_star {ι : Type*} [LinearOrder ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hgm : MonotoneOn g (Set.Ici 0))
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : EmmonsTardiness.SPT.IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (A : Finset ι) (hAJ : A ⊆ J) (hkA : k ∉ A)
    (h1 : ∃ l : List ι, IsOptimal g p d J l ∧ ∀ i ∈ A, EmmonsTardiness.SPT.Precedes l k i)
    (h2 : d k < d j)
    (h3 : ∑ i ∈ J \ A, p i ≤ d j + p j) :
    ∃ l : List ι, IsOptimal g p d J l ∧ (∀ i ∈ A, EmmonsTardiness.SPT.Precedes l k i) ∧ EmmonsTardiness.SPT.Precedes l k j := by sorry

end EmmonsTardiness.EDD

