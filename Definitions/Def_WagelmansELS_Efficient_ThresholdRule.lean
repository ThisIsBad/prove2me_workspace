import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient
namespace Instance
variable (P : Instance)

/-- The next efficient period after `t`; the default is the sentinel. -/
noncomputable def succ (i t : ℕ) : ℕ :=
  let S := (E P i).filter (fun u => t < u)
  if h : S.Nonempty then S.min' h else P.n + 1

/-- Slope between consecutive efficient points. -/
noncomputable def ratio (i t : ℕ) : ℝ :=
  (P.G t - P.G (succ P i t)) / (P.D t - P.D (succ P i t))

/-- The first efficient period whose slope to its successor is below `c_i`,
or the sentinel if there is none. -/
noncomputable def q (i : ℕ) : ℕ :=
  let S := insert (P.n + 1)
    ((E P i).filter (fun t => t < P.n + 1 ∧ ratio P i t < P.c i))
  S.min' (by simp [S])

end Instance
end WagelmansELS.Efficient
