import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.Local

/-- Semismoothness, Qi–Sun (1993), p. 355: `F` is locally Lipschitz at `x` and, for every
direction `h`, the limit `lim_{V ∈ ∂F(x + t h'), h' → h, t ↓ 0} V h'` exists (called `L`). -/
def SemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
  ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
    ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

/-- `p`-order semismoothness, Qi–Sun (1993), p. 358: `F` is semismooth at `x` and
`V h - F'(x; h) = O(‖h‖^{1+p})` for `V ∈ ∂F(x + h)`, `h → 0`, pinned as: there are `C` and
`δ > 0` with `‖V h - F'(x; h)‖ ≤ C ‖h‖^{1+p}` whenever `‖h‖ < δ` and `V ∈ ∂F(x + h)`.
The paper's range `0 < p ≤ 1` is a hypothesis of every statement that uses it. -/
def POrderSemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (p : ℝ) (F : E → G) (x : E) : Prop :=
  SemismoothAt F x ∧ ∃ C δ : ℝ, 0 < δ ∧ ∀ h : E, ‖h‖ < δ → ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + h),
    ∀ d : G, HasDirDerivAt F x h d → ‖V h - d‖ ≤ C * ‖h‖ ^ (1 + p)

end NonsmoothNewton.Local
