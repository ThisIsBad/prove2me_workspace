import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model

namespace RoslingAssembly.Unbounded

namespace Model

variable (S : Model)

/-- The greatest total lead time `max_{k ∈ {i} ∪ B(i)} M_k` in the subsystem `{i} ∪ B(i)`
(M_m of the proof of Theorem 4(i), p. 578). -/
noncomputable def Mmax (i : ℕ) : ℕ := (insert i (S.B i)).sup S.M

/-- The "one more unit" policy of the proof of Theorem 4(i) (p. 578), with `δ` extra units:
for every item `k ∈ {i} ∪ B(i)` it raises Y_kt by `δ` in every period `t ≥ M_m − M_k + 1`
(Lean period `k' ≥ M_m − M_k`), so that the extra units are ordered of `k` in period
`M_m − M_k + 1` and held in stock forever; all other decisions are those of `π`. -/
noncomputable def perturb (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) : RoslingAssembly.SeriesEquiv.Policy :=
  fun k' x j => π k' x j + if j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ k' then δ else 0

end Model

end RoslingAssembly.Unbounded
