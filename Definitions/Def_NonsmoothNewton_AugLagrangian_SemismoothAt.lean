import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Semismoothness, Qi–Sun (1993), p. 355: `F` is locally Lipschitz at `x` and, for every
direction `h`, the limit `lim_{V ∈ ∂F(x + t h'), h' → h, t ↓ 0} V h'` exists (called `L`). -/
def SemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
  ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
    ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

end NonsmoothNewton.AugLagrangian
