import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Eqs. (2.6)–(2.7) (p. 836), from the proof of Theorem 2.1: the per-step descent
inequality (2.6) for Algorithm 1 against any fixed point `z*` of `T`, and its summed form
(2.7), stated with a lower bound `c ≤ λ_i` in place of the printed `λ_k`. -/
theorem descent_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (zs : H) (hzs : zs ∈ Function.fixedPoints (threeOp γ JA JB C)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    (∀ k : ℕ,
        ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
          + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2) ∧
      ∀ c : ℝ, 0 < c → (∀ j, c ≤ lam j) → ∀ k : ℕ,
        Summable (fun i : ℕ => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2) ∧
          ∑' i : ℕ, ‖C (xB (k + i)) - C (JB zs)‖ ^ 2
            ≤ ‖z k - zs‖ ^ 2 / (γ * c * (2 * β - γ / ε)) := by sorry

end ThreeOpSplitting.Convergence

