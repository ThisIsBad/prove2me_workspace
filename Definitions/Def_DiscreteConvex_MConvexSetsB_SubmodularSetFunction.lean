import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103-104, Eq. (4.9)-(4.10): submodular set
functions, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- `ρ : 2ⱽ → R ∪ {+∞}` is a **submodular set function** with `ρ(∅) = 0` and `ρ(V) < +∞`
(the class `S[R]`, Eq. (4.10)): `ρ(X) + ρ(Y) ≥ ρ(X ∪ Y) + ρ(X ∩ Y)` for all `X, Y ⊆ V`
(Eq. (4.9)). -/
def SubmodularSetFunction {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → WithTop ℝ) :
    Prop :=
  ρ ∅ = 0 ∧ ρ Finset.univ ≠ ⊤ ∧
    ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)

end DiscreteConvex.MConvexSetsB
