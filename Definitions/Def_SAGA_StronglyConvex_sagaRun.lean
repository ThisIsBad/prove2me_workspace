import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaStep

namespace SAGA.StronglyConvex

/-- The SAGA state `(x^k, φ^k)` after `k` iterations started at `x^0` with `φ_i^0 = x^0` for all `i`,
when the indices drawn at iterations `1, …, k` are `js 0, …, js (k-1)`. -/
noncomputable def sagaRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (P : E → E) (γ : ℝ) (x0 : E) :
    (k : ℕ) → (Fin k → Fin n) → E × (Fin n → E)
  | 0, _ => (x0, fun _ => x0)
  | k + 1, js => sagaStep f' P γ (sagaRun f' P γ x0 k (fun t => js (Fin.castSucc t))) (js (Fin.last k))

end SAGA.StronglyConvex
