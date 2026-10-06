import Mathlib
import Definitions.Def_SAGA_Convex_sagaStep

namespace SAGA.Convex

/-- The SAGA state after applying the steps with the indices of the list `l`, in order, from the
initial state `(x^0, φ^0)` with `φᵢ^0 = x^0` for every `i` (p. 2). -/
noncomputable def sagaRun {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (l : List (Fin n)) :
    EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) :=
  l.foldl (sagaStep f' P γ) (x0, fun _ => x0)

/-- The iterate `x^t` for the index sequence `js = (j^1, …, j^k)`: the iterate after the first
`t` steps (for `t ≤ k`; it uses only the first `t` indices). -/
noncomputable def sagaIterate {d n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (js : Fin k → Fin n) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (sagaRun f' P γ x0 ((List.ofFn js).take t)).1

/-- The averaged iterate `x̄^k = (1/k) ∑_{t=1}^k x^t` (Theorem 2, p. 11), which excludes `x^0`. -/
noncomputable def avgIterate {d n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (js : Fin k → Fin n) : EuclideanSpace ℝ (Fin d) :=
  (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, sagaIterate f' P γ x0 js (t + 1)

/-- The expectation over `k` independent indices, each uniform on `Fin n`: the uniform average
`(1/n^k) ∑_{js : Fin k → Fin n} g(js)`. -/
noncomputable def expectIdx (n k : ℕ) (g : (Fin k → Fin n) → ℝ) : ℝ :=
  (1 / (n : ℝ) ^ k) * ∑ js, g js

end SAGA.Convex
