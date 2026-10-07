import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

namespace TalagrandConc.QPoints

/-- The two observations (3.1.6) of the induction step of Theorem 3.1.1: with
`B i` the projection of `A i ⊆ Ω^{N+1}` on `Ω^N` and `A i (ω)` its section,
`f(A, (x, ω)) ≤ 1 + f(B, x)`, and for each `j`, `f(A, (x, ω)) ≤ f(C, x)` where
`C i = B i` for `i ≠ j` and `C j = A j (ω)`. -/
theorem eq_3_1_6 {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by sorry

end TalagrandConc.QPoints

