import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Algorithm

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- §5, p. 389: in every run of the multicut algorithm for simple recourse problems,
(a) Step 1 is solved at most `J m2 + 1` times: if the `ν`-th solve of Step 1 takes place, then
`ν ≤ J m2 + 1`; and
(b) when the algorithm stops at `x^ν`, `x^ν` is an optimal solution of the simple recourse problem
(3), (19)–(20). -/
theorem multicut_simple_recourse_bound (inst : Instance n1 m1 m2 J) :
    (∀ ν I, Reach inst ν I → ν ≤ J * m2 + 1) ∧
    ∀ ν I x, Reach inst ν I → StopsAt inst I x → IsOptimal inst x := by sorry

end MulticutLShaped.SimpleRecourse

