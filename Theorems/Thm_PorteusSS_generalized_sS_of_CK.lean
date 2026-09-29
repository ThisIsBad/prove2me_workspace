import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Theorem 2 (p. 415). In the model of §§II–III, if for a period `n ≥ 1` every
`G_{κ n} = κ· + h_n` (`κ ∈ C`) lies in `C(K_κ)` and `Y_n(x)` is nonempty for every `x`,
then a generalized `(s, S)` policy is optimal in period `n`. -/
theorem generalized_sS_of_CK (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hG : ∀ κ ∈ slopeSet c, CK (Kc c κ) (Gfn c m φ f0 α κ n))
    (hY : ∀ x : ℝ, (Yset c m φ f0 α n x).Nonempty) :
    ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x := by sorry

end PorteusSS
