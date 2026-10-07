import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_MonotoneHomogeneous

/-!
# Theorem 2.11.1: the Crandall-Tartar theorem (§2.11.1, p.154)
-/

namespace PalmQueueing.Recurrence

/-- **Theorem 2.11.1** (the Crandall-Tartar theorem, p.154). If `φ` is homogeneous, then it is
monotone **if and only if** it is non-expansive.

The theorem establishes a link between monotonicity and non-expansiveness, two properties that
have nothing to do with each other in general: homogeneity is what ties them together. It is why
§2.11 can call its subject "non-expansive stochastic recurrences" while every model it treats is
built from monotone maps, and it is what lets Kingman's sub-additive ergodic theorem be applied to
those models.

One direction is a two-line computation from monotonicity and homogeneity,
`φ(x) = φ(y + (x − y)) ≤ φ(y + (max_i(xⁱ − yⁱ))1) = φ(y) + (max_i(xⁱ − yⁱ))1 ≤ φ(y) + ‖x − y‖_∞ 1`,
and the symmetric relation with `x` and `y` interchanged. The other uses non-expansiveness on
`x` and `x + a e_i` for the canonical basis vectors.

The equivalence is stated as an equivalence, not as one implication: both directions are the
theorem, and the useful one in §2.11 is that monotone-and-homogeneous models are automatically
non-expansive. -/
theorem crandall_tartar {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ)
    (hhom : IsHomogeneousMap phi) :
    IsMonotoneMap phi ↔ IsNonExpansiveMap phi := by sorry

end PalmQueueing.Recurrence

