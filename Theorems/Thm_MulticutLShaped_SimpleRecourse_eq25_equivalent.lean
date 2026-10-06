import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- (24)–(25), p. 389: the simple recourse problem (3), (19)–(20) is equivalent to the LP (25).
For every `x ∈ K₁`, with `χ = Tx`, the choice `u_ij = max(0, p_ij q_ij (h_ij − χ_i))` is feasible
for (25), minimizes the (25) objective among all `u` feasible with `(x, χ)`, and the minimum equals
`cx + Ψ(Tx)`. Consequently `x` is optimal for (3) iff `(x, χ, u)` is optimal for (25) for some
`χ, u`. -/
theorem eq25_equivalent (inst : Instance n1 m1 m2 J) :
    (∀ x ∈ K1 inst,
      Feasible25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) ∧
      ((obj25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) : ℝ)
          : EReal) = z inst x ∧
      ∀ u, Feasible25 inst x (inst.T.mulVec x) u →
        obj25 inst x (inst.T.mulVec x)
            (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i)))
          ≤ obj25 inst x (inst.T.mulVec x) u) ∧
    ∀ x, IsOptimal inst x ↔ ∃ χ u, IsOptimal25 inst x χ u := by sorry

end MulticutLShaped.SimpleRecourse

