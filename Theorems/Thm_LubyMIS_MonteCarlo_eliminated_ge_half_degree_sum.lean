import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- First display of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), for an arbitrary random
selection `I′ = S ω` drawn with probabilities `w ω`:
`E[Y_k − Y_{k+1}] ≥ ½ ∑_i d(i) Pr[i ∈ I′ ∪ N(I′)] ≥ ½ ∑_i d(i) Pr[i ∈ N(I′)]`. -/
theorem eliminated_ge_half_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (S : Ω → Finset V) :
    (∑ ω, w ω * (eliminated H (S ω) : ℝ)) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ nbhd H (S ω) then w ω else 0) := by sorry

end LubyMIS.MonteCarlo
