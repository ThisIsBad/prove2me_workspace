import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

/-- LEMMA 1 (Luby 1986, §4.2, p. 1045). On the `q²`-point sample space of §4.2, with the uniform law,
`Pr[X_i = R_j] = n_{ij}/q`. -/
theorem lemma1 (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i : Fin n) (r : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r)).card : ℝ) / (q : ℝ) ^ 2 =
      (nCount A i r : ℝ) / q := by sorry

end LubyMIS.Derandomized
