import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_HasPSDLift

namespace ConeLifts.StableSet

/-- **Theorem 5.2** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): let `G` be any graph
with `n` vertices. Then `STAB(G)` does not admit a `Sⁿ₊`-lift.

All lifts are excluded, proper or not: there is no affine subspace `L` of the real `n × n`
matrices and no linear map `π` to `ℝⁿ` with `STAB(G) = π(Sⁿ₊ ∩ L)`. The hypothesis `n ≥ 1` is
the paper's reading of "a graph with n vertices": for `n = 0`, `STAB(G) = {0} = π(S⁰₊)` and the
printed statement fails. -/
theorem stab_no_psd_lift (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    ¬ HasPSDLift n (stab G) := by sorry

end ConeLifts.StableSet

