import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed
import Definitions.Def_MDPFinance_PDMDP_Process

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
  [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.2.7 (Bäuerle–Rieder, p. 253-254, PDF 264-265). Under the hypotheses of Theorem
8.2.6, if the flow `φ_t^α(x)` is independent of `α` (uncontrolled flow), or if `U` is convex,
`μ(x,u)` is linear in `u` and `u ↦ r(x,u) + λ ∫ J^{rel}_∞(z) Q(dz|x,u)` is concave on `U`, then
there exists an optimal **nonrelaxed** stationary Markov policy `π^*_t = f(Z_n)(t-T_n)`,
`f : E → A` measurable, and `V_∞ = J_∞ = J^{rel}_∞`; in particular `V_∞` is a fixed point of
`T`. "`U` convex, `μ` linear in `u`" is stated through an injective continuous embedding
`Uemb : U → V` of the control space into a real normed space `V` (the book's `U` is a convex
Borel subset of such a space): `Uemb '' U` convex, `μ(x,·) = L_x ∘ Uemb` with `L_x` linear, and
concavity along convex combinations taken in `V`. `V_∞` is read as `J_∞` of the nonrelaxed
embedded model (`JinfSup`), per Theorem 8.2.1. -/
theorem theorem_8_2_7 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b)
    (Uemb : U → V) (hUemb_cont : Continuous Uemb) (hUemb_inj : Function.Injective Uemb)
    (hcase :
      (∀ t x (α α' : ℝ → U), Measurable α → Measurable α' → Mk.φ t α x = Mk.φ t α' x) ∨
        (Convex ℝ (Set.range Uemb) ∧
          (∀ x, ∃ Lx : V →ₗ[ℝ] E, ∀ u, Mk.μ (x, u) = Lx (Uemb u)) ∧
          ∀ x (u v w : U) (a c : ℝ), 0 ≤ a → 0 ≤ c → a + c = 1 →
            Uemb w = a • Uemb u + c • Uemb v →
            (a : EReal) * (((Mk.r (x, u) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, u)) (JrelInfSup Mk EmbR)) +
              (c : EReal) * (((Mk.r (x, v) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, v)) (JrelInfSup Mk EmbR)) ≤
            ((Mk.r (x, w) : ℝ) : EReal) +
              (Mk.lam : EReal) * erealIntegral (Mk.Q (x, w)) (JrelInfSup Mk EmbR))) :
    ∃ f : E → ControlFn U, Measurable f ∧
      (∀ x, JinfEmbed Mk Emb (fun _ => f) x = JinfSup Mk Emb x) ∧
      (∀ x, JinfSup Mk Emb x = JrelInfSup Mk EmbR x) ∧
      ∀ x, JinfSup Mk Emb x = TEmbed Mk Emb (JinfSup Mk Emb) x := by sorry

end MDPFinance.PDMDP
