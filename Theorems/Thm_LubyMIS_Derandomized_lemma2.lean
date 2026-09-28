import Mathlib
import Definitions.Def_LubyMIS_Derandomized_SampleSpace

namespace LubyMIS.Derandomized

/-- LEMMA 2 (Luby 1986, §4.2, p. 1045). On the `q²`-point sample space of §4.2, with the uniform law,
for distinct vertices `i ≠ i′`: `Pr[X_i = R_j and X_{i′} = R_{j′}] = n_{ij} n_{i′j′} / q²`. -/
theorem lemma2 (q : ℕ) [Fact q.Prime] (n : ℕ) (hnq : n ≤ q) {R : Type*} [DecidableEq R]
    (A : Fin n → ZMod q → R) (i i' : Fin n) (hii' : i ≠ i') (r r' : R) :
    ((Finset.univ.filter (fun p : ZMod q × ZMod q => Xrv A i p = r ∧ Xrv A i' p = r')).card : ℝ) /
        (q : ℝ) ^ 2 =
      ((nCount A i r : ℝ) * (nCount A i' r' : ℝ)) / (q : ℝ) ^ 2 := by sorry

end LubyMIS.Derandomized
