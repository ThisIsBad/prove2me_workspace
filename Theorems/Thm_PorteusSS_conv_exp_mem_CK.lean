import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 10 (p. 424). If `f ∈ C_a(K)` for `a ∈ ℝ` and `φ` is the exponential density with
parameter `lam > 0`, then `f * φ ∈ C(K)`. -/
theorem conv_exp_mem_CK (a K lam : ℝ) (f : ℝ → ℝ) (hf : CaK a K f) (hlam : 0 < lam) :
    CK K (conv f (expDensity lam)) := by sorry

end PorteusSS
