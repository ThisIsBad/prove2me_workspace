import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, p. 725 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"For each s and f, the sth coordinate of V_β(f) is a rational function of β, as the
representation V = (I − βQ)⁻¹r shows."

For every decision rule `f` and state `s` there are real polynomials `p`, `q` such that `q`
does not vanish on `[0, 1)` and `V_β(f^(∞))_s = p(β)/q(β)` for every `β ∈ [0, 1)`.

**Formalization Note.** The nonvanishing of the denominator on all of `[0, 1)` is part of the
statement; without it `q = 0` would be a junk witness, since `x / 0 = 0` in Lean. -/
theorem value_rational {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∀ (f : St → Act) (s : St), ∃ p q : Polynomial ℝ,
      (∀ β : ℝ, 0 ≤ β → β < 1 → q.eval β ≠ 0) ∧
      ∀ β : ℝ, 0 ≤ β → β < 1 → M.V β (stationary f) s = p.eval β / q.eval β := by sorry

end BlackwellDiscreteDP.Stationary

