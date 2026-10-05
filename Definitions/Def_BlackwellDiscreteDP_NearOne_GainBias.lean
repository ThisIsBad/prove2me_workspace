import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

namespace Model

variable {St Act : Type*} [Fintype St] [DecidableEq St] (M : Model St Act)

/-- `Q*(f)`: the limit matrix `Q*` associated with `Q(f)`. Blackwell (1962), p. 722,
Theorem 4. -/
noncomputable def Qstar (f : St → Act) : Matrix St St ℝ := limitMatrix (M.Q f)

/-- `H(f)`: the matrix `H = (I − Q(f) + Q*(f))⁻¹ − Q*(f)` of Lemma 1(d) associated with `Q(f)`.
Blackwell (1962), p. 723, proof of Theorem 4(a). -/
noncomputable def Hf (f : St → Act) : Matrix St St ℝ := deviationMatrix (M.Q f)

/-- `x(f) = Q*(f) r(f)` (the gain, or average income, of `f^(∞)`).

Blackwell (1962), p. 722, Theorem 4(a), and p. 723, proof of (a).

**Formalization Note.** The paper defines `x(f)` as the unique solution of
`(I − Q(f))x = 0, Q*(f)x = Q*(f)r(f)`; its proof of (a) identifies it as `Q*(f)r(f)`. The
closed form is taken as the definition, and the theorem formalizing Theorem 4(a) asserts that it
is the unique solution of that system. -/
noncomputable def x (f : St → Act) : St → ℝ := M.Qstar f *ᵥ M.r f

/-- `y(f) = H(f) r(f)` (the bias of `f^(∞)`).

Blackwell (1962), p. 722, Theorem 4(a), and p. 723, proof of (a).

**Formalization Note.** The paper defines `y(f)` as the unique solution of
`(I − Q(f))y = r(f) − x(f), Q*(f)y = 0`; its proof of (a) identifies it as `H(f)r(f)`. The
closed form is taken as the definition, and the theorem formalizing Theorem 4(a) asserts that it
is the unique solution of that system. -/
noncomputable def y (f : St → Act) : St → ℝ := M.Hf f *ᵥ M.r f

/-- Theorem 4(b)'s set `G(s, f)` (no `β`): the actions `a` for which either
`p(s, a)x(f) > x_s(f)`, or `p(s, a)x(f) = x_s(f)` and
`i(s, a) + p(s, a)y(f) > x_s(f) + y_s(f)`. Blackwell (1962), pp. 722–723, Theorem 4(b).

**Formalization Note.** Distinct from Theorem 3's β-dependent `G(s, f)`
(`betaImprovementSet`). -/
def gainBiasImprovementSet (f : St → Act) (s : St) : Set Act :=
  {a | M.pDot s a (M.x f) > M.x f s ∨
        (M.pDot s a (M.x f) = M.x f s ∧ M.i s a + M.pDot s a (M.y f) > M.x f s + M.y f s)}

/-- Theorem 4(c)'s set `E(s, f)`: the actions `a` with `p(s, a)x(f) = x_s(f)` and
`i(s, a) + p(s, a)y(f) = x_s(f) + y_s(f)`. Blackwell (1962), p. 723, Theorem 4(c). -/
def gainBiasEqualSet (f : St → Act) (s : St) : Set Act :=
  {a | M.pDot s a (M.x f) = M.x f s ∧ M.i s a + M.pDot s a (M.y f) = M.x f s + M.y f s}

end Model

end BlackwellDiscreteDP.NearOne
