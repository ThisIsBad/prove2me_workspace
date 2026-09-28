import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem radical_eq_sInf_maximal_eq_iInf_pointIdeal {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) :
    J.radical = sInf {m | J ≤ m ∧ m.IsMaximal} ∧
      J.radical = ⨅ a ∈ zeroSet J, pointIdeal a := by sorry

end Nullstellensatz
