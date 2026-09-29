import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration
import Definitions.Def_ThreeOpSplitting_Convergence_RegularityConditions

open Filter Topology

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Theorem 2.1 (Main convergence theorem), p. 835, Parts 1 and 2. -/
theorem main_convergence_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hlam_inf : 0 < ⨅ j, lam j) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    let xA := xASeq γ JA JB C lam z0
    ∃ zs ∈ Function.fixedPoints T, WeakTendsto z zs ∧
      -- Part 1(a)
      (∀ xs ∈ zer (opSum A B C), Tendsto (fun j => C (xB j)) atTop (𝓝 (C xs))) ∧
      -- Part 1(b)
      WeakTendsto xB (JB zs) ∧ JB zs ∈ zer (opSum A B C) ∧
      -- Part 1(c)
      WeakTendsto xA (JB zs) ∧
      -- Part 2
      ((IsUniformlyMonotoneOnBounded A ∨ IsUniformlyMonotoneOnBounded B ∨
          ∀ x ∈ zer (opSum A B C), IsDemiregularAt C x) →
        ∃ xs ∈ zer (opSum A B C), Tendsto xB atTop (𝓝 xs) ∧ Tendsto xA atTop (𝓝 xs)) := by sorry

end ThreeOpSplitting.Convergence

