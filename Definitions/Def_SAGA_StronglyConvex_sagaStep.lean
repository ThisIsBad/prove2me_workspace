import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaW

namespace SAGA.StronglyConvex

/-- One iteration of SAGA (Section 2, p. 2) from the state `s = (x^k, φ^k)` with index `j`:
`x^{k+1} = P (w^{k+1})` (eq. (2), `P` playing the role of `prox_γ^h`) and the table entry `j`
is overwritten by `x^k` (`φ_j^{k+1} = x^k`), all other entries unchanged. -/
noncomputable def sagaStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (P : E → E) (γ : ℝ) (s : E × (Fin n → E)) (j : Fin n) :
    E × (Fin n → E) :=
  (P (sagaW f' γ s.1 s.2 j), Function.update s.2 j s.1)

end SAGA.StronglyConvex
