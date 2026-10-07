import Mathlib
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Proof of Theorem 3(b) (p. 15), the displayed chain: with `c = Σ_{j ∈ S} a_j − ½A`,
`k(S) = k(T) − (Σ_{j∈S} a_j)(Σ_{j∈T−S} a_j) = Σ_{j,k∈T, j≤k} a_j a_k − (½A + c)(½A − c) = y + c²`. -/
theorem theorem_3b_k_identity (a : List ℕ) (S : Finset (Fin a.length)) :
    let c : ℝ := ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2
    (kVal a S : ℝ) =
        (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) ∧
      (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) =
        (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) ∧
      (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) = yB a + c ^ 2 := by sorry

end SchedComplexity.Partition

