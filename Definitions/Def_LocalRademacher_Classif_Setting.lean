import Mathlib
import Definitions.Def_UnderstandingML_Rademacher

namespace LocalRademacher.Classif

/-- The **discrete loss** `ℓ(y, y') = 1[y ≠ y']` of §6.2 (Bartlett, Bousquet & Mendelson,
arXiv:math/0508275v1, p. 28). It is defined on all of `ℝ` rather than on `{±1}` because the
quantity `J(μ)` of Theorem 6.3 evaluates it at `sign(σᵢ + μYᵢ)`, which can be `0`. -/
noncomputable def ell (y y' : ℝ) : ℝ := if y = y' then 0 else 1

/-- The empirical loss `(1/n) ∑ᵢ ℓ(f(Xᵢ), zᵢ)` of the classifier `f` against the label vector `z` on
the inputs `xs = (X₁, …, Xₙ)`. With `z = Y` this is `Pₙℓ_f = Pₙℓ(f(X), Y)`; with `z = σ` (a sign
vector) it is `Pₙℓ(f(X), σ)` (pp. 3, 5, 29). -/
noncomputable def empLoss {X : Type*} {n : ℕ} (xs : Fin n → X) (z : Fin n → ℝ) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ell (f (xs i)) (z i)

/-- The evaluation vectors `(ℓ(f(X₁), Y₁), …, ℓ(f(Xₙ), Yₙ))` of the loss functions `ℓ_f` of the
classifiers `f ∈ F` with `Pₙℓ_f ≤ b`. The empirical Rademacher average
`E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ b}` of p. 28 is `UnderstandingML.rademacher (lossVecs F xs ys b)`. -/
def lossVecs {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (xs : Fin n → X) (ys : Fin n → ℝ) (b : ℝ) :
    Set (Fin n → ℝ) :=
  {v | ∃ f ∈ F, empLoss xs ys f ≤ b ∧ v = fun i => ell (f (xs i)) (ys i)}

/-- The weighted empirical risk minimum of Theorem 6.3 (p. 29), for a fixed sign vector `σ` and
`μ ≥ 0`:
`J(μ) = min_{f ∈ F} (1/n) ∑ᵢ |σᵢ + μYᵢ| ℓ(f(Xᵢ), sign(σᵢ + μYᵢ))`.
The infimum is the real infimum over the subtype `F`; the theorems that use `J` assume `F`
nonempty, and the summands take finitely many values, so it is attained. `Real.sign 0 = 0`
where the page's `sign` is undefined; such a term has weight `|σᵢ + μYᵢ| = 0`, so the convention
does not affect the value. -/
noncomputable def J {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (xs : Fin n → X) (ys : Fin n → ℝ)
    (σ : Fin n → Bool) (μ : ℝ) : ℝ :=
  ⨅ f : F, (1 / (n : ℝ)) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i| *
    ell ((f : X → ℝ) (xs i)) (Real.sign (UnderstandingML.signVec σ i + μ * ys i))

/-- The empirical local Rademacher complexity of the classification loss class
(Corollary 6.2, p. 28, with the generic multiplier `c` of Theorem 6.3 in place of `20`):
`ψ̂ₙ(r) = c sup_{α ∈ [√(2r), 1]} α E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ 2r/α²} + 26x/n`.
The supremum is the real supremum over the subtype `[√(2r), 1]`; it is a true supremum when
`0 < r ≤ 1/2` (nonempty range, bounded values), which the theorems assume. -/
noncomputable def psiHat {X : Type*} {n : ℕ} (c x r : ℝ) (F : Set (X → ℝ)) (xs : Fin n → X)
    (ys : Fin n → ℝ) : ℝ :=
  c * (⨆ α : Set.Icc (Real.sqrt (2 * r)) 1,
      (α : ℝ) * UnderstandingML.rademacher (lossVecs F xs ys (2 * r / (α : ℝ) ^ 2)))
    + 26 * x / n

end LocalRademacher.Classif
