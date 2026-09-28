import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem jacobson_of_finiteType {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsJacobsonRing R] [Algebra.FiniteType R A] :
    IsJacobsonRing A ∧
      ∀ m : Ideal A, m.IsMaximal →
        (m.comap (algebraMap R A)).IsMaximal ∧
          Module.Finite (R ⧸ m.comap (algebraMap R A)) (A ⧸ m) := by sorry

end Nullstellensatz
