import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Lemma 6.2, p. 134. Let `A` be closed and `B` closable, and let `ρ(A) ≠ ∅` (needed for
"for one `z ∈ ρ(A)`" to be satisfiable; see the moderation notes). Then are equivalent:
(i) `B` is `A` bounded; (ii) `𝔇(A) ⊆ 𝔇(B)`; (iii) `BR_A(z)` is bounded (everywhere defined, finite
norm) for one `z ∈ ρ(A)`; (iii') the same for all `z ∈ ρ(A)`. Moreover, for `A` bounded `B`, the
`A`-bound of `B` is at most `inf_{z ∈ ρ(A)} ‖BR_A(z)‖`. -/
theorem relativelyBounded_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hB : B.IsClosable)
    (hρ : (resolventSet A).Nonempty) :
    [IsRelativelyBounded A B,
      A.domain ≤ B.domain,
      ∃ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤,
      ∀ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤].TFAE ∧
    (IsRelativelyBounded A B →
      relativeBound A B ≤ ⨅ z ∈ resolventSet A, opNorm (compCLM B (resolvent A z))) := by sorry

end TeschlQM.KatoRellich
