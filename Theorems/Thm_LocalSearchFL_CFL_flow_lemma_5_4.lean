import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.4**, p. 560: for any two CFL solutions `X` and `O`, in the flow graph with an
edge `(v_s, w_o)` of length `c_{so}` for every copy `s` of `X` and copy `o` of `O`, and an edge
`(w_o, sink)` of length `f_o / u_o`, one can simultaneously route `|N_X(s)|` units of flow
from every `v_s` to the sink at total cost at most `cost_s(X) + cost_s(O) + cost_f(O)`.
Here `x s o` is the (integer-valued) flow on the path `v_s → w_o → sink`. -/
theorem flow_lemma_5_4 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) :
    ∃ x : Fin X.n → Fin O.n → ℕ,
      (∀ s, ∑ o, x s o = (X.nbhd s).card) ∧
      ∑ s, ∑ o, (x s o : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by sorry

end LocalSearchFL.CFL
