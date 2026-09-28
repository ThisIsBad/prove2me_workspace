import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem zariski_lemma {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.FiniteType K L] :
    Module.Finite K L := by sorry

end Nullstellensatz
