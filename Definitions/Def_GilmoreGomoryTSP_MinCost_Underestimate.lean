import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

/-- The interval (15) `P_q = [B_q, B_{q+1}] ∩ [A_{φ(q)}, A_{φ(q+1)}]`, for the adjacent pair
`q.castSucc`, `q.succ` (the paper's `q`, `q + 1`). -/
def Pq (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) : Set ℝ :=
  Set.Icc (B q.castSucc) (B q.succ) ∩ Set.Icc (A (φ q.castSucc)) (A (φ q.succ))

/-- The set (16) `P = ⋃_{q=1}^{N−1} P_q`. -/
def P (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) : Set ℝ :=
  ⋃ q, Pq A B φ q

/-- The underestimating cost (17) of having job `j` follow job `i`:
`c*_ij = |[B_i, +∞] ∩ [−∞, A_j] ∩ P|_f + |[−∞, B_i] ∩ [A_j, +∞] ∩ P|_g`, where `|S|_f = ∫_S f`. -/
noncomputable def cStar (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : ℝ :=
  (∫ x in Set.Icc (B i) (A j) ∩ P A B φ, f x) + ∫ x in Set.Icc (A j) (B i) ∩ P A B φ, g x

/-- The underestimate `c*(ψ) = ∑_i c*_{i ψ(i)}` (p. 665). -/
noncomputable def costStar (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) :
    ℝ :=
  ∑ i, cStar f g A B φ i (ψ i)

/-- The adjacent arcs `R_{q,q+1}` for which (22a) `i ≤ q < φ⁻¹ψ(i)` holds for some `i` or (22b)
`φ⁻¹ψ(j) ≤ q < j` holds for some `j` (here `q` stands for the lower node `q.castSucc`). -/
def starArcs (φ ψ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    (∃ i, i ≤ q.castSucc ∧ q.castSucc < φ.symm (ψ i)) ∨
      ∃ j, φ.symm (ψ j) ≤ q.castSucc ∧ q.castSucc < j

/-- The graph `G_ψ*` (p. 668): all the arcs of `G_φ`, plus every arc `R_{q,q+1}` for which (22a)
holds for some `i` or (22b) holds for some `j`. -/
def graphStar (φ ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  graphWith φ (adjArcs (starArcs φ ψ))

end GilmoreGomoryTSP.MinCost
