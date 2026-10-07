import Mathlib

open MeasureTheory

namespace RadGauss.Classification

/-- The real-valued class `{x ↦ f(x) ∈ {−1, 1} ⊆ ℝ : f ∈ F}` of a class `F` of `{±1}`-valued
functions; labels `{±1}` are encoded as the units `ℤˣ = {1, -1}` of `ℤ`, coerced to `ℝ`. -/
def realClass {X : Type*} (F : Set (X → ℤˣ)) : Set (X → ℝ) :=
  (fun f x => ((f x : ℤ) : ℝ)) '' F

/-- The **misclassification probability** `P(Y ≠ f(X))` of a `{±1}`-valued function `f` under a
probability distribution `P` on `X × {±1}` (Bartlett–Mendelson 2002, Theorem 5, p. 465). -/
noncomputable def classError {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    (f : X → ℤˣ) : ℝ :=
  P.real {z | z.2 ≠ f z.1}

/-- The **training error** `P̂_n(Y ≠ f(X)) = (1/n) #{i : Y_i ≠ f(X_i)}` of `f` on the sample
`S = ((X_1, Y_1), …, (X_n, Y_n))`, where `P̂_n` is the empirical measure of the sample
(p. 463). Sample indices are 0-based (`Fin n`). -/
noncomputable def trainError {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (f : X → ℤˣ) : ℝ :=
  ((Finset.univ.filter fun i => (S i).2 ≠ f (S i).1).card : ℝ) / n

/-- `sup_{h ∈ L∘F} (E h − Ê_n h)` for the 0–1 loss `L(Y, f(X)) = 1(Y ≠ f(X))`
(Appendix B, p. 480): the largest gap, over `f ∈ F`, between the misclassification
probability and the training error on the sample `S`. A real supremum; the gaps lie in
`[−1, 1]`, so it is a genuine supremum for nonempty `F` (and `0` for empty `F`). -/
noncomputable def gapSup {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    (F : Set (X → ℤˣ)) {n : ℕ} (S : Fin n → X × ℤˣ) : ℝ :=
  ⨆ f : F, (classError P f - trainError S f)

/-- The double-sample supremum `sup_{f ∈ F} (P̂'_n(Y ≠ f(X)) − P̂_n(Y ≠ f(X)))` of the
training-error differences on a ghost sample `S'` and the sample `S` (Appendix B, p. 480,
the symmetrization that follows the proof of Theorem 8, p. 468). -/
noncomputable def ghostGapSup {X : Type*} (F : Set (X → ℤˣ)) {n : ℕ}
    (S S' : Fin n → X × ℤˣ) : ℝ :=
  ⨆ f : F, (trainError S' f - trainError S f)

end RadGauss.Classification
