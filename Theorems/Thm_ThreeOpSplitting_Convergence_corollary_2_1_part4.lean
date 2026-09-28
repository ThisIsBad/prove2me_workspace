import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

open Filter Topology

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Corollary 2.1, Part 4 (p. 835): if `τ̲ := inf_j τ_j > 0` then
`‖T z^k - z^k‖² ≤ ‖z^0 - z*‖² / (τ̲ (k + 1))` for every `z* ∈ Fix T`, and
`‖T z^k - z^k‖² = o(1/(k+1))`. -/
theorem corollary_2_1_part4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hτinf : 0 < ⨅ j, tau ε (lam j)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    (∀ zs ∈ Function.fixedPoints T, ∀ k : ℕ,
        ‖T (z k) - z k‖ ^ 2 ≤ ‖z0 - zs‖ ^ 2 / ((⨅ j, tau ε (lam j)) * ((k : ℝ) + 1))) ∧
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) * ‖T (z k) - z k‖ ^ 2) atTop (𝓝 0) := by sorry

end ThreeOpSplitting.Convergence

