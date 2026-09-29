import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§1.3.1 (small print)**, Arrow & Debreu, Econometrica 22 (1954), p. 269 (PDF p. 6): the
quasi-concavity of `u_i` — the set `{x_i | x_i ∈ X_i and u_i(x_i) ≧ α}` is convex for every real
`α` — "is indeed implied by III.c. (but is obviously weaker)".

**Formalization Note.** The paper's proof uses III.a ("Then, from III.a., we can find x⁴ …") and
the convexity of `X_i` (Assumption II), so both are hypotheses: III.c alone does not imply
quasi-concavity (on `ℝ`, `u = −1` at one point and `0` elsewhere satisfies III.c). Mathlib's
`QuasiconcaveOn ℝ s f` says exactly that every upper level set `{x ∈ s | r ≤ f x}` is convex. -/
theorem quasiconcave_of_IIIc {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIa : AssumptionIIIa E) (hIIIc : AssumptionIIIc E) :
    ∀ i, QuasiconcaveOn ℝ (E.X i) (E.u i) := by sorry

end ArrowDebreu.ThmI
