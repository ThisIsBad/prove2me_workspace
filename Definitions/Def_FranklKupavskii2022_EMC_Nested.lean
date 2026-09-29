import Mathlib

namespace FranklKupavskii2022.EMC

/-- Nested families (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 4, p. 9): "We say that
F_1, …, F_{s+1} are nested if F_1 ⊃ F_2 ⊃ … ⊃ F_{s+1}" (non-strict inclusions).

**Formalization Note.** The families are `Fam 1, …, Fam (s + 1)`; values of `Fam` outside
`1..s+1` are ignored. -/
def Nested (s : ℕ) (Fam : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ s + 1 → Fam j ⊆ Fam i

end FranklKupavskii2022.EMC
