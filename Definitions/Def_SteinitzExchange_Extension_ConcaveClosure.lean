import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension

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

/-- The maximizers of a real function `f` on a set `S ⊆ ℝ^V`:
`{b ∈ S | f(b) ≥ f(c) ∀ c ∈ S}` (Murota 1996, p. 285, Eq. (4.6), with `S = B̄`). -/
def argmaxOn {V : Type*} (S : Set (V → ℝ)) (f : (V → ℝ) → ℝ) : Set (V → ℝ) :=
  {b | b ∈ S ∧ ∀ c ∈ S, f c ≤ f b}

end SteinitzExchange.Extension
