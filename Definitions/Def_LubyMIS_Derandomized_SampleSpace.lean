import Mathlib

namespace LubyMIS.Derandomized

/-- The random variable `X_i` on the `q²`-point sample space of §4.2 (Luby 1986, p. 1044): at the
sample point `b^{x,y}`, `X_i` takes the value `b_i = A_{i,(x + y·i) mod q}`. Row `i` of the `n × q`
matrix `A` is `A i : ZMod q → R`, and the vertex label is `(i : ℕ) ∈ {0, …, n − 1}`. -/
def Xrv {n q : ℕ} {R : Type*} (A : Fin n → ZMod q → R) (i : Fin n) (p : ZMod q × ZMod q) : R :=
  A i (p.1 + p.2 * ((i : ℕ) : ZMod q))

/-- `n_{ij}`: the number of entries of row `i` of `A` equal to the value `r` (§4.2, p. 1044). -/
def nCount {n q : ℕ} [NeZero q] {R : Type*} [DecidableEq R] (A : Fin n → ZMod q → R) (i : Fin n)
    (r : R) : ℕ :=
  (Finset.univ.filter (fun l => A i l = r)).card

end LubyMIS.Derandomized
