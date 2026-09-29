import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), (2.1), p. 210: the *conjugate* of `f : V → (−∞, +∞]` is the function
on the dual `V* = StrongDual ℝ V` given by `f*(x*) = sup {⟨x, x*⟩ − f(x) | x ∈ V}`,
computed in `EReal` (so `f*` may take the value `+∞`). The biconjugate `f**` is
`conj (conj f)`, a function on the bidual `StrongDual ℝ (StrongDual ℝ V)`. -/
noncomputable def conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) :
    StrongDual ℝ V → EReal :=
  fun x' => ⨆ x : V, ((x' x : ℝ) : EReal) - f x

end RockafellarMaxMono.Shared
