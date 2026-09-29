import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6):
`Rε,p(PN,ℓ) = sup_{Q ∈ Bε,p(PN)} R(Q,ℓ)`, the supremum of the nominal risk over the
ambiguity set. Valued in `EReal` (rather than `ℝ`) so the supremum is a genuine least upper
bound with no junk value: Mathlib's real-valued `sSup`/`⨆` defaults to `0` on an unbounded or
empty family, which would silently misstate an unbounded worst-case risk as `0`. The
`Integrable` guard on `ℓ` under each candidate `Q` prevents Mathlib's separate junk value for
the Bochner integral of a non-integrable function (`0`) from contaminating the supremum. -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : Q ∈ ambiguitySet ε p Ξ PN) (_ : Integrable ℓ Q),
    (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Duality
