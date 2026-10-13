import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Theorem 7.5 (Balas, *Disjunctive Programming*, Springer 2018, §7.2, p. 93, [99]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with `p = |N'|` 0-1 variables,
`N^p(K) = conv(K₀)`, where `N¹(K) := N(K)` and `N^t(K) := N(N^{t-1}(K))`. The iterates are given
by systems `(A t, b t)`, `t = 0,…,p`, with `Poly (A 0) (b 0) = K` and
`Poly (A (t+1)) (b (t+1)) = N(Poly (A t) (b t))`. Every system contains the bound rows `x ≥ 0`,
`x_j ≤ 1` (`j ∈ N'`) (`HasBoundRows`), as `Ãx ≥ b̃` does in the book; each `N^t(K) ⊆ K` lies in
the box, so such a representation always exists (append the redundant bound rows), and it makes
the linearized system of `N` equal to Lovász and Schrijver's representation-free cone
formulation.
Corrected: the retired version allowed systems without the bound rows. -/
theorem lovasz_schrijver_reaches_hull_v2 {n p : ℕ} {mA : Fin (p + 1) → ℕ}
    (A : (t : Fin (p + 1)) → Matrix (Fin (mA t)) (Fin n) ℝ)
    (b : (t : Fin (p + 1)) → Fin (mA t) → ℝ) (Nprime : Finset (Fin n)) (hp : Nprime.card = p)
    (hK : ∀ t, HasBoundRows (A t) (b t) Nprime)
    (hStep : ∀ t : Fin p, Poly (A t.succ) (b t.succ) = NOp (A t.castSucc) (b t.castSucc) Nprime) :
    Poly (A (Fin.last p)) (b (Fin.last p)) = convexHull ℝ (K0Set (A 0) (b 0) Nprime) := by sorry

end Disjunctive.HigherDim

