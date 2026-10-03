import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.BayesianModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- A (stationary) Markov policy: a sequence of decision rules `π : ℕ → E → A`, `π k` used when
`k` stages remain. -/
def MPolicy (E A : Type*) := ℕ → E → A

/-- `π` uses a feasible decision rule at every stage. -/
def IsMPolicyOf (D : Set (E × A)) (π : MPolicy E A) : Prop := ∀ k, IsDecisionRuleOf D (π k)

/-- `V_k^π(x) := r(x,π_k(x)) + β ∫ V_{k-1}^π(x') Q(dx'|x,π_k(x))`, `V_0^π(x) := g(x)`
(Bäuerle–Rieder, p. 18, PDF 33, unnumbered display defining `V_n^π`, specialized to a stationary
model and re-indexed by stages-remaining `k`, matching `MDPFinance.Bellman.Vpi`/`TfChain`
(chunk `02a`)'s pattern but time-homogeneous). -/
noncomputable def VpiOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (π : MPolicy E A) : (k : ℕ) → E → EReal
  | 0, x => g x
  | (k + 1), x => r (x, π k x) + (β : EReal) * erealIntegral (Q (x, π k x))
      (VpiOf D Q r g β π k)

/-- `𝔼^π_x[Σ_{j<k} β^j r⁺(X_j,A_j) + β^k g⁺(X_k)] ∈ [0,∞]`, the same recursion for the positive
parts `r⁺`, `g⁺` (Lebesgue integrals). -/
noncomputable def VposOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (π : MPolicy E A) : (k : ℕ) → E → ℝ≥0∞
  | 0, x => (g x ⊔ 0).toENNReal
  | (k + 1), x => (r (x, π k x) ⊔ 0).toENNReal + ENNReal.ofReal β *
      ∫⁻ x', VposOf D Q r g β π k x' ∂(Q (x, π k x))

/-- The Integrability Assumption (AN) of Chapter 2 (Bäuerle–Rieder, p. 18, PDF 33), stationary
form, for horizon `N`: for every number `k ≤ N` of stages to go and every state `x`,
`sup_π 𝔼^π_x[Σ_{j<k} β^j r⁺(X_j,A_j) + β^k g⁺(X_k)] < ∞`. Restated from
`MDPFinance.Bellman.IntegrabilityAssumption` (chunk `02a`). -/
def IntegrabilityOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (N : ℕ) : Prop :=
  ∀ k ≤ N, ∀ x : E, (⨆ π ∈ {π : MPolicy E A | IsMPolicyOf D π}, VposOf D Q r g β π k x) < ⊤

/-- `V_k(x) := sup_{π \text{ feasible}} V_k^π(x)`, the *true* (sup-over-policies) value function
with `k` stages remaining (Bäuerle–Rieder, p. 18, PDF 33). This is the object Theorem 5.4.8
(via Theorem 2.3.8) asserts satisfies the Bellman recursion against `Top`/`TChain` — a genuine,
non-definitional fact, exactly as `MDPFinance.Bellman.structure_theorem` (chunk `02a`) is for the
finite-horizon `V`. -/
noncomputable def Vsup (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (k : ℕ) (x : E) : EReal :=
  ⨆ π ∈ {π : MPolicy E A | IsMPolicyOf D π}, VpiOf D Q r g β π k x

end MDPFinance.BayesianModels
