import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

open Filter Topology

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Corollary 2.1, Parts 1–3 (pp. 834–835): Krasnosel'skiĭ–Mann convergence of
Algorithm 1. The printed comparison `α < 2β/(4β - γ)` is not a hypothesis (it contradicts
`γ < 2βε`), and `τ_k` is the coefficient used in the proof (p. 836). -/
theorem corollary_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    (∀ zs ∈ Function.fixedPoints T, Antitone (fun j => ‖z j - zs‖)) ∧
      Antitone (fun j => ‖T (z j) - z j‖) ∧
      Tendsto (fun j => ‖T (z j) - z j‖) atTop (𝓝 0) ∧
      ∃ zs ∈ Function.fixedPoints T, WeakTendsto z zs ∧ JB zs ∈ zer (opSum A B C) := by sorry

end ThreeOpSplitting.Convergence

