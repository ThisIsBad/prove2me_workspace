import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
  [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.3.3 (Bäuerle–Rieder, p. 261, PDF 272). Suppose the finite-horizon continuous-time
Markov Decision Chain has an upper bounding function `b` and the continuity and compactness
assumptions (i)-(iv) of Theorem 8.3.1 hold. Then there exists an optimal Markov policy `π^*_t =
f^*(t,X_{t-})`, `t ∈ [0,T]`, for a measurable decision rule `f^* : E' → U`, `f^*(t,x)` a maximum
point of `u ↦ r(x,u) + Σ_y q_{xy}(u) V(t,y)`; the policy `(f_n)` with `f_n(t,x)(s) := f^*(t+s,x)`
attains `V` on `E' = [0,T] × E`. Moreover `V` is a fixed point of `T` in `IB_b^+`: `V(t,x) =
e^{-λ(T-t)} g(x) + ∫_0^{T-t} e^{-λs} sup_{u∈U} [r(x,u) + λ Σ_y V(t+s,y) Q({y}|x,u)] ds`. -/
theorem theorem_8_3_3 (Ch : MDChainFinite E U) (b : E → ℝ) (cr cg cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChainFinite Ch b cr cg cQ)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)) :
    (∃ fstar : ℝ → E → U, Measurable (fun p : ℝ × E => fstar p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x,
          ((Ch.r (x, fstar t x) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar t x)) (Ch.Vinf t) -
                Ch.Vinf t x) =
            ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) (Ch.Vinf t) - Ch.Vinf t x))) ∧
        ∃ f : ℕ → ℝ → E → ControlFn U, IsChainPolicyFinite f ∧
          (∀ n t x s, (f n t x).1 s = fstar (t + s) x) ∧
          ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Jinf f t x = Ch.Vinf t x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Vinf t x = Ch.T Ch.Vinf t x := by sorry

end MDPFinance.PDMDP
