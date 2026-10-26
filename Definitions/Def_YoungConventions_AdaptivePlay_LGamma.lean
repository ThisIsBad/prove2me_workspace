import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_shortestPathLength

namespace YoungConventions.AdaptivePlay

/-- **`L_Γ = maxₛ L(s)`** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§4, p. 64, PDF p. 9): "let `L_Γ = maxₛ L(s)`".

`LGamma u` is the maximum, over all strategy tuples `s ∈ ∏ Sᵢ`, of the length `L(s)` of a shortest
best-reply path from `s` to a strict Nash equilibrium.

**Formalization Note.** The maximum over the finite set `∏ Sᵢ` is `Finset.univ.sup` (in `ℕ`, the
supremum of the empty family would be `0`, but `∏ Sᵢ` is nonempty when every `Sᵢ` is). The value is
meaningful for weakly acyclic games; see `shortestPathLength`. -/
noncomputable def LGamma {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (u : ι → (∀ i, S i) → ℝ) : ℕ :=
  Finset.univ.sup (shortestPathLength u)

end YoungConventions.AdaptivePlay
