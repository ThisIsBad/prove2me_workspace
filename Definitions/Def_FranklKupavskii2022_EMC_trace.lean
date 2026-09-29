import Mathlib

namespace FranklKupavskii2022.EMC

/-- The family `F(S)` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2, p. 4): "For any
S ⊂ [s + 1], define the family F(S) by F(S) := {F − S : F ∈ F, F ∩ [s + 1] = S}."

**Formalization Note.** `[s + 1] = Finset.Icc 1 (s + 1)`. `F(∅)` is `trace s F ∅`, the family of
members of `F` that avoid `[s + 1]`; the paper's `∂F(S)` is Mathlib's shadow `∂ (trace s F S)`
(`Finset.shadow`, scoped notation in `FinsetFamily`), which for a uniform family is exactly the
paper's immediate shadow. -/
def trace (s : ℕ) (F : Finset (Finset ℕ)) (S : Finset ℕ) : Finset (Finset ℕ) :=
  (F.filter (fun A => A ∩ Finset.Icc 1 (s + 1) = S)).image (· \ S)

end FranklKupavskii2022.EMC
