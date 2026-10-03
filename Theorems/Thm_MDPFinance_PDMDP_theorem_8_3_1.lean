import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory Filter

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.3.1 (Bäuerle–Rieder, p. 257, PDF 268). Suppose the continuous-time Markov Decision
Chain has an upper bounding function `b` with `α_b < 1` (`c_Q λ/(β+λ) < 1`, the book's bound
`α_b ≤ c_Q λ/(β+λ)`) and (i) `U` compact, (ii) `u ↦ q_{xy}(u)` continuous, (iii) `u ↦ Σ_y b(y)
q_{xy}(u)` continuous (rendered through `Σ_y b(y) Q({y}|x,u) = b(x) + λ^{-1} Σ_y b(y) q_{xy}(u)`),
(iv) `u ↦ r(x,u)` upper semicontinuous. Then a) `V_∞ ∈ IB_b^+` and `V_∞` is a fixed point of
`T`, i.e. `β V_∞(x) = sup_{u∈U} [r(x,u) + Σ_y q_{xy}(u) V_∞(y)]` (with `Σ_y q_{xy}(u) V_∞(y) =
λ(∫ V_∞ dQ(·|x,u) - V_∞(x))`); b) there is an optimal stationary Markov policy `π^*_t = f^*(X_{t-})`
for a measurable `f^* : E → U`, `f^*(x)` a maximum point of `u ↦ r(x,u) + Σ_y q_{xy}(u) V_∞(y)`.
`V_∞` is the chain's value through its embedded model (`Vinf`, Theorem 8.2.1). -/
theorem theorem_8_3_1 (Ch : MDChain E U) (b : E → ℝ) (cr cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChain Ch b cr cQ) (hαb : cQ * (Ch.lam / (Ch.β + Ch.lam)) < 1)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)) :
    (Ch.Vinf ∈ IBbPlus b ∧
        ∀ x, (Ch.β : EReal) * Ch.Vinf x = ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
          (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
      ∃ fstar : E → U, Measurable fstar ∧
        (∀ x, ((Ch.r (x, fstar x) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar x)) Ch.Vinf - Ch.Vinf x) =
          ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
        ∀ x, Ch.Jinf (fun _ => fstar) x = Ch.Vinf x := by sorry

end MDPFinance.PDMDP
