import Mathlib

namespace FoundationsML.RademacherVC

/-- The growth function of a hypothesis set `H` of functions `X → Bool` (Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.6,
p. 34, PDF p. 51): `Π_H(m)` is the maximum, over sets (here: tuples) of `m` points of `X`, of
the number of distinct dichotomies (labelings) `H` realizes on those points.

**Formalization Note.** Points are taken as a tuple `x : Fin m → X` rather than a size-`m`
subset of `X`; allowing repeated points never increases the dichotomy count (a repeated point
cannot add a new labeling), so the supremum over tuples equals the book's supremum over
size-`m` sets whenever `X` has at least `m` distinct points, and is a harmless generalization
otherwise. `Fin m → Bool` is finite, so the inner cardinality — and hence this supremum over
`ℕ` — is always bounded (by `2^m`), with no vacuous/unbounded-supremum corner. -/
noncomputable def GrowthFunction {X : Type*} (H : Set (X → Bool)) (m : ℕ) : ℕ :=
  ⨆ x : Fin m → X, Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x}

end FoundationsML.RademacherVC
