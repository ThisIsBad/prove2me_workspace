import Mathlib
import Definitions.Def_NonsmoothNewton_Global_clarkeJac

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- `F` is semismooth at `x` (Qi–Sun 1993, p. 355): `F` is locally Lipschitzian at `x` and, for
every direction `h`, the limit of `V h'` over `V ∈ ∂F(x + t h')`, `h' → h`, `t ↓ 0` exists. -/
def SemismoothAt (F : E → G) (x : E) : Prop :=
  (∃ K, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
    ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
      ∀ V ∈ clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

end NonsmoothNewton.Global
