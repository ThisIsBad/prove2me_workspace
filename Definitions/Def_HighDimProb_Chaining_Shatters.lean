import Mathlib

namespace HighDimProb.Chaining

/-- **`Shatters F Λ`**: the class `F` of Boolean functions on `Ω` shatters the subset `Λ ⊆ Ω` if
every function `g : Λ → Bool` arises as the restriction to `Λ` of some `f ∈ F`. Vershynin,
*High-Dimensional Probability* (2018), Definition 8.3.1, p. 200 (PDF p. 208): "We say that a
subset `Λ ⊆ Ω` is shattered by `F` if any function `g : Λ → {0, 1}` can be obtained by
restricting some function `f ∈ F` onto `Λ`." `Bool` stands for the book's `{0, 1}`. -/
def Shatters {Ω : Type} (F : Set (Ω → Bool)) (Λ : Set Ω) : Prop :=
  ∀ g : Λ → Bool, ∃ f ∈ F, ∀ x : Λ, f x.1 = g x

end HighDimProb.Chaining
