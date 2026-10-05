import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 3, pp. 720–721 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593), the policy improvement theorem for a fixed
`β ∈ [0, 1)`. With `G(s, f)` the set of actions `a` such that
`i(s, a) + βp(s, a)V(f^(∞)) > V_s(f^(∞))`:

1. if `G(s, f)` is empty for all `s`, then `f^(∞)` is optimal (§3 sense, against all policies);
2. for any `g` such that (a) `g(s) ∈ G(s, f)` for some `s` and (b) `g(s) = f(s)` whenever
   `g(s) ∉ G(s, f)`, we have `g^(∞) > f^(∞)`, where `>` is "≧ coordinatewise and ≠". -/
theorem theorem_3 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) :
    ((∀ s : St, M.G β f s = ∅) → M.IsBetaOptimal β (stationary f)) ∧
    (∀ g : St → Act, (∃ s : St, g s ∈ M.G β f s) →
        (∀ s : St, g s ∉ M.G β f s → g s = f s) →
        M.V β (stationary f) ≤ M.V β (stationary g) ∧
          M.V β (stationary g) ≠ M.V β (stationary f)) := by sorry

end BlackwellDiscreteDP.Stationary

