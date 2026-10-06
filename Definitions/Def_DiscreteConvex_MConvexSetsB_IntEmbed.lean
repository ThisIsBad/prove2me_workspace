import Mathlib

/-!
The real embedding `Zⱽ ↪ Rⱽ` of a set of integer vectors, used to state the hole-free
property (Theorem 4.12) and related closure identities (Murota, *Discrete Convex Analysis*,
SIAM 2003, pp.107-116), in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The real embedding `\{(x(v):ℝ) : x ∈ B\}` of a set `B ⊆ Zⱽ` of integer vectors. -/
def IntEmbed {V : Type*} (B : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' B

end DiscreteConvex.MConvexSetsB
