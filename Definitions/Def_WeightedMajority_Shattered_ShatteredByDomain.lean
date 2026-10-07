import Mathlib

namespace WeightedMajority.Shattered

/-- A family of Boolean functions is shattered by its domain when every joint
pattern of their values occurs at an instance (Littlestone--Warmuth, p. 244). -/
def ShatteredByDomain {X : Type*} {n : ℕ} (φ : Fin n → X → Bool) : Prop :=
  ∀ b : Fin n → Bool, ∃ x : X, ∀ i : Fin n, φ i x = b i

end WeightedMajority.Shattered
