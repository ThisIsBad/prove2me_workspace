import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality

/-- The concave conjugate `g°(p) = min{⟨p, x⟩ − g(x) | x ∈ B}` of `g : B → ℝ` for a nonempty
finite `B ⊆ ℤ^V` (Murota 1996, p. 284, Eq. (4.1)). For nonempty `B` the infimum over the finite
index set is the minimum; for empty `B` the value is the junk value `0`, and every statement
assumes `B` nonempty. -/
noncomputable def concaveConj {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (p : V → ℝ) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), (pairing p (toReal (x : V → ℤ)) - g x)

/-- The concave closure `ĝ(b) = inf{⟨p, b⟩ − g°(p) | p ∈ ℝ^V}` (Murota 1996, p. 284, Eq. (4.2)).
For `b ∈ B̄` the family is bounded below (by `min g`) and this real infimum is the paper's value;
for `b ∉ B̄` the paper's value is `−∞` and this real infimum is the junk value `0`, so every
statement uses `concaveClosure` only at points of `B̄` (the paper regards `ĝ` as `ĝ : B̄ → ℝ`). -/
noncomputable def concaveClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (b : V → ℝ) : ℝ :=
  ⨅ p : V → ℝ, (pairing p b - concaveConj B g p)

/-- The convex conjugate `f•(p) = max{⟨p, x⟩ − f(x) | x ∈ B}` of `f : B → ℝ` for a nonempty
finite `B ⊆ ℤ^V` (Murota 1996, p. 293, Eq. (6.1)). For nonempty `B` the supremum over the finite
index set is the maximum; for empty `B` the value is the junk value `0`, and every statement
assumes `B` nonempty. -/
noncomputable def convexConj {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (p : V → ℝ) : ℝ :=
  ⨆ x : (B : Set (V → ℤ)), (pairing p (toReal (x : V → ℤ)) - f x)

/-- The convex closure `f̌(b) = sup{⟨p, b⟩ − f•(p) | p ∈ ℝ^V}` (Murota 1996, p. 293, Eq. (6.2)).
For `b ∈ B̄` the family is bounded above (by `max f`) and this real supremum is the paper's value;
for `b ∉ B̄` the paper's value is `+∞` (Eq. (6.3)) and this real supremum is the junk value `0`,
so every statement uses `convexClosure` only at points of `B̄` (the paper regards `f̌` as
`f̌ : B̄ → ℝ`). -/
noncomputable def convexClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (b : V → ℝ) : ℝ :=
  ⨆ p : V → ℝ, (pairing p b - convexConj B f p)

end SteinitzExchange.Duality
