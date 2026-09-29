import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

variable {l m n : ℕ}

/-- **Assumption I.a** (§1.2.2, p. 267, PDF p. 4): `Y_j` is a closed convex subset of `R^l`
containing `0` (`j = 1, ⋯, n`). -/
def AssumptionIa (E : Economy l m n) : Prop :=
  ∀ j, IsClosed (E.Y j) ∧ Convex ℝ (E.Y j) ∧ (0 : Fin l → ℝ) ∈ E.Y j

/-- **Assumption I.b** (§1.2.2, p. 267, PDF p. 4): `Y ∩ Ω = 0`, i.e. the aggregate production set
meets the nonnegative orthant exactly in `{0}` ("= 0" is equality with the set `{0}`). -/
def AssumptionIb (E : Economy l m n) : Prop :=
  aggProd E ∩ Ω l = {0}

/-- **Assumption I.c** (§1.2.2, p. 267, PDF p. 4): `Y ∩ (−Y) = 0`, equality with the set `{0}`. -/
def AssumptionIc (E : Economy l m n) : Prop :=
  aggProd E ∩ negSet (aggProd E) = {0}

/-- **Assumption II** (§1.3.0, p. 268, PDF p. 5): for every consumer `i`, `X_i` is a closed convex
subset of `R^l` which is bounded from below, i.e. there is a vector `ξ_i` with `ξ_i ≦ x_i` for all
`x_i ∈ X_i` (componentwise order). -/
def AssumptionII (E : Economy l m n) : Prop :=
  ∀ i, IsClosed (E.X i) ∧ Convex ℝ (E.X i) ∧ ∃ ξ : Fin l → ℝ, ∀ x ∈ E.X i, ξ ≤ x

/-- **Assumption III.a** (§1.3.1, p. 269, PDF p. 6): `u_i` is a continuous function on `X_i`, for
every consumer `i`. -/
def AssumptionIIIa (E : Economy l m n) : Prop :=
  ∀ i, ContinuousOn (E.u i) (E.X i)

/-- **Assumption III.b** (§1.3.1, p. 269, PDF p. 6): for any `x_i ∈ X_i` there is `x_i' ∈ X_i`
with `u_i(x_i') > u_i(x_i)` (no satiation), for every consumer `i`. -/
def AssumptionIIIb (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∃ x' ∈ E.X i, E.u i x < E.u i x'

/-- **Assumption III.c** (§1.3.1, p. 269, PDF p. 6): if `u_i(x_i) > u_i(x_i')` and `0 < t < 1`,
then `u_i[t x_i + (1 − t) x_i'] > u_i(x_i')`, for every consumer `i` and all `x_i, x_i' ∈ X_i`. -/
def AssumptionIIIc (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∀ x' ∈ E.X i, E.u i x' < E.u i x →
    ∀ t : ℝ, 0 < t → t < 1 → E.u i x' < E.u i (t • x + (1 - t) • x')

/-- **Assumption IV.a** (§1.3.2, p. 270, PDF p. 7): `ζ_i ∈ R^l`, and for some `x_i ∈ X_i`,
`x_i < ζ_i`, for every consumer `i`.

**Formalization Note.** The paper's `x < y` means `x_h < y_h` for *every* component `h` (§1.2.1);
it is written `∀ h, x h < ζ i h`, not with Lean's `<` on `Fin l → ℝ` (which means `≤` and `≠`). -/
def AssumptionIVa (E : Economy l m n) : Prop :=
  ∀ i, ∃ x ∈ E.X i, ∀ h, x h < E.ζ i h

/-- **Assumption IV.b** (§1.3.2, p. 270, PDF p. 7): for all `i, j`, `α_{ij} ≧ 0`; for all `j`,
`Σ_{i=1}^m α_{ij} = 1`. -/
def AssumptionIVb (E : Economy l m n) : Prop :=
  (∀ i j, 0 ≤ E.α i j) ∧ ∀ j, ∑ i, E.α i j = 1

/-- **Assumptions I–IV** (§§1.2.2–1.3.2, pp. 267–270, PDF pp. 4–7), the hypotheses of Theorem I:
I.a, I.b, I.c, II, III.a, III.b, III.c, IV.a and IV.b, each a separate field. -/
structure AssumptionsItoIV (E : Economy l m n) : Prop where
  Ia : AssumptionIa E
  Ib : AssumptionIb E
  Ic : AssumptionIc E
  II : AssumptionII E
  IIIa : AssumptionIIIa E
  IIIb : AssumptionIIIb E
  IIIc : AssumptionIIIc E
  IVa : AssumptionIVa E
  IVb : AssumptionIVb E

end ArrowDebreu.ThmI
