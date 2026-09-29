import Mathlib

/-!
# The random point associated with a limit permutation, and the density `t(τ, Z)`

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2: Definition 2.3 (p. 9), the joint distribution function (Sect. 2.1,
p. 6), Definitions 1.4, 3.2 and 3.3 with Eqs. (23)–(24) (pp. 4, 10–11), and the event `A_τ`
(Sect. 5.1, p. 16).

A definition bundle: the quantile function of `Z(x, ·)`, the law `μ_Z` of the random point
`(X, Y)` associated with `Z`, the joint distribution function of a measure on `[0,1]²`, the event
`A_τ`, and the density `t(τ, Z)`.

**Formalization Note.** Probabilities are the real-valued `Measure.real`. The random point of
Definition 2.3 (draw `X ∼ U[0,1]`, then `Y` with cdf `Z(X, ·)`) is realized by the inverse-cdf
(quantile) construction: `(X, Y) = (U₁, Q_Z(U₁, U₂))` with `(U₁, U₂)` uniform on `[0,1]²`,
where `Q_Z(x, u) = inf {y ∈ [0,1] : u ≤ Z(x, y)}`. For a cdf `F = Z(x, ·)` one has
`Q_Z(x, u) ≤ y ↔ u ≤ F(y)`, so `Q_Z(x, U₂)` has cdf `F`; the agreement of this construction with
the paper's joint distribution function is the milestone Eq. (21). `Measure.map` returns the zero
measure for a map that is not almost-everywhere measurable; for `Z ∈ 𝒵` the map is
almost-everywhere measurable, and every statement using `limitMeasure Z` assumes `Z ∈ 𝒵`.
-/

namespace PermLimits.Shared

open MeasureTheory unitInterval

/-- The **quantile function** of the cdf `Z(x, ·)`: `Q_Z(x, u) = inf {y ∈ [0,1] : u ≤ Z(x, y)}`
(the inverse-cdf transform used to realize Definition 2.3 of Hoppen et al.,
arXiv:1103.5844v2, p. 9).

**Formalization Note.** The infimum is taken in the complete lattice `I = [0,1]`. When `Z(x, ·)`
is a cdf the set contains `1`, since `Z(x, 1) = 1 ≥ u`, so the infimum is over a nonempty set.
-/
noncomputable def quantile (Z : I → I → ℝ) (x u : I) : I :=
  sInf {y : I | (u : ℝ) ≤ Z x y}

/-- The **law `μ_Z` of the random point `(X, Y)` associated with `Z`** (Hoppen et al.,
arXiv:1103.5844v2, Definition 2.3, p. 9): first `X ∼ U[0, 1]`, then, given `X`, `Y` is drawn with
cdf `Z(X, ·)`.

**Formalization Note.** Realized as the image of the uniform (Lebesgue) measure on `[0,1]²`
under `(x, u) ↦ (x, Q_Z(x, u))`; see the module note. -/
noncomputable def limitMeasure (Z : I → I → ℝ) : Measure (I × I) :=
  (volume : Measure (I × I)).map (fun p => (p.1, quantile Z p.1 p.2))

/-- The **joint distribution function** of a measure `μ` on `[0,1]²` (Hoppen et al.,
arXiv:1103.5844v2, Sect. 2.1, p. 6): `F(x, y) = P(X ≤ x, Y ≤ y) = μ([0, x] × [0, y])`. -/
noncomputable def jointCDF (μ : Measure (I × I)) (x y : I) : ℝ :=
  μ.real (Set.Iic x ×ˢ Set.Iic y)

/-- The **event `A_τ`** (Hoppen et al., arXiv:1103.5844v2, Sect. 5.1, p. 16; the relation of
Definition 3.2, Eq. (23), p. 10): the set of `k`-tuples of points `(x_i, y_i)` of `[0,1]²` such
that the relative order of the vertical coordinates, read in increasing order of the horizontal
coordinates, is `τ`.

**Formalization Note.** `ρ` lists the indices in increasing order of the horizontal coordinates
(the paper's `R⁻¹`), and the vertical coordinate of the `i`-th point in that order has rank
`τ(i)` (the paper's `S ∘ R⁻¹ = τ`). Both conditions are strict, so tuples with a repeated
horizontal or vertical coordinate are not in `A_τ` (the paper notes these have probability zero).
-/
def patternEvent {k : ℕ} (τ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  {p | ∃ ρ : Equiv.Perm (Fin k),
    (∀ i j, i < j → (p (ρ i)).1 < (p (ρ j)).1) ∧
    ∀ i j, ((p (ρ i)).2 < (p (ρ j)).2 ↔ τ i < τ j)}

/-- The **density of `τ` in `Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 3.3, Eq. (24),
p. 11): `t(τ, Z) = P(σ(k, Z) = τ)`, where `σ(k, Z)` is the `Z`-random permutation of length `k`
(Definitions 1.4 and 3.2): for `k` i.i.d. random points `(X_i, Y_i)` with the law `μ_Z`,
`σ(k, Z) = S ∘ R⁻¹` records the relative order of the `Y`'s read in increasing order of the
`X`'s.

**Formalization Note.** `t(τ, Z) = μ_Z^{⊗k}(A_τ)` with `μ_Z = limitMeasure Z` and
`A_τ = patternEvent τ`; this is the identity (47) of the paper, p. 16. -/
noncomputable def limitDensity {k : ℕ} (τ : Equiv.Perm (Fin k)) (Z : I → I → ℝ) : ℝ :=
  (Measure.pi fun _ : Fin k => limitMeasure Z).real (patternEvent τ)

end PermLimits.Shared
