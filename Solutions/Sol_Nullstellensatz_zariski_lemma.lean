import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

end Nullstellensatz

open Nullstellensatz

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.FiniteType K L] :
    Module.Finite K L :=
  finite_of_finite_type_of_isJacobsonRing K L
