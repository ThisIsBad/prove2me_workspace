import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated

/-!
# Steuer–Choo (1983), §2: the ideal criterion vector

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §2, p. 327.

`z*ᵢ = max {fᵢ(x) | x ∈ S} + εᵢ`, where a given `εᵢ ≥ 0` (`εᵢ = 0` is permissible) unless
(i) there is more than one nondominated criterion vector that maximizes the `i`th objective, or
(ii) the only nondominated criterion vector that maximizes the `i`th objective also maximizes one of
the other objectives, in which case `εᵢ` must be strictly positive.

`max {fᵢ(x) | x ∈ S}` is the maximum of the `i`-th coordinate over `Z`.
-/

namespace SteuerChoo.Discrete

/-- Condition (i) of §2, p. 327: more than one nondominated criterion vector maximizes the `i`-th
objective. -/
def CondI {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, ∃ w ∈ nondominated Z, z ≠ w ∧ MaximizesObj Z i z ∧ MaximizesObj Z i w

/-- Condition (ii) of §2, p. 327: the only nondominated criterion vector that maximizes the `i`-th
objective also maximizes one of the other objectives. -/
def CondII {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, MaximizesObj Z i z ∧
    (∀ w ∈ nondominated Z, MaximizesObj Z i w → w = z) ∧
    ∃ j, j ≠ i ∧ MaximizesObj Z j z

/-- `IsIdealVector Z zstar`: `zstar` is an ideal criterion vector for `Z` in the sense of §2, p. 327:
there are `εᵢ ≥ 0` with `z*ᵢ = max_{z ∈ Z} zᵢ + εᵢ` for every `i` (the maximum being attained), and
`εᵢ > 0` whenever condition (i) or (ii) holds for objective `i`. -/
def IsIdealVector {k : ℕ} (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ) : Prop :=
  ∃ ε : Fin k → ℝ, (∀ i, 0 ≤ ε i) ∧
    (∀ i, ∃ z, MaximizesObj Z i z ∧ zstar i = z i + ε i) ∧
    ∀ i, (CondI Z i ∨ CondII Z i) → 0 < ε i

end SteuerChoo.Discrete
