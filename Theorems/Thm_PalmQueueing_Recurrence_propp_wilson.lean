import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_ExactSampling

/-!
# Theorem 2.5.1: the Propp-Wilson coupling-from-the-past theorem (§2.5.3, p.112)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.5.1** (p.112). The backwards coalescence time `N⁻` is almost surely finite. In
addition, the random variable `Z = X_0^{-N⁻}(i)` has the distribution `π`.

**Exactly `π`**, not approximately and not in the limit. That is what makes coupling from the past
an *exact sampling* algorithm and why Propp and Wilson's construction matters: a statement that
the law of `X_n` converges to `π` is a different and already classical result. The proof gets it
from `P(N⁻ ≤ k) = P(N⁺ ≤ k)` (Property 2.5.2), the a.s. finiteness of the forwards coalescence
time `N⁺` (Property 2.5.1), and the fact that `X_0^{-n}(i) = Z` for every `n ≥ N⁻`, so that
`P(Z = j) = lim_n P(X_0^{-n}(i) = j) = lim_n IPⁿ_{ij} = π(j)`.

`Z` is characterised rather than constructed: the second clause says that **any** random variable
agreeing with the common value of the coalesced chains has law `π`, which is (2.5.10) without an
inf. The value does not depend on `i`, which the first clause supplies. -/
theorem propp_wilson {r : ℕ} (C : CFTP Ω r) (i₀ : Fin r) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.Coalesced n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.Coalesced n ω → Z ω = C.X (-(n : ℤ)) n i₀ ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by sorry

end PalmQueueing.Recurrence

