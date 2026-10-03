import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
  [TopologicalSpace A]

/-- `\mathrm{Ls}\,D_n(x)`, the upper limit of a sequence of sets (Bäuerle–Rieder, p. 201, PDF
212): `a` is an accumulation point of *some* sequence `(a_n)` with `a_n \in D_n` for every `n` —
stated exactly as the book's own definition (a statement about a sequence of *points*, not a
`Filter.limsup` of sets), via Mathlib's `MapClusterPt`. -/
def LsSeq (Dn : ℕ → Set A) : Set A :=
  {a | ∃ an : ℕ → A, (∀ n, an n ∈ Dn n) ∧ MapClusterPt a atTop an}

/-- A set-valued map `x ↦ D(x)` is upper semicontinuous (Bäuerle–Rieder, Appendix Definition
A.2.1a, p. 351, PDF 358, restated from `MDPFinance.Semicontinuous.USCSetValued`, chunk `02b`, per
this chunk's file-ownership boundary): sequence-based, as the book's own remark that this is
"slightly more restrictive" than other literature definitions. -/
def USCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ as : ℕ → A, (∀ n, as n ∈ D (xs n)) → ∃ a ∈ D x, MapClusterPt a atTop as

/-- A set-valued map is continuous (Bäuerle–Rieder, Appendix Definition A.2.1c) if it is upper
*and* lower semicontinuous — lower semicontinuity restated directly here since Theorem 7.3.6 is
this chunk's only consumer of "continuous" `x ↦ D(x)`. -/
def ContinuousSetValued (D : E → Set A) : Prop :=
  USCSetValued D ∧
    ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
      ∀ a ∈ D x, ∃ as : ℕ → A, (∀ n, as n ∈ D (xs n)) ∧ MapClusterPt a atTop as

/-- `D^*_{J}(x) := \{a \in D(x) \mid a \text{ is a maximum point of } a \mapsto LJ(x,a)\}`
(Bäuerle–Rieder, p. 201, PDF 212, `D_n^*`/`D_\infty^*`/`D^*` all instances of this one shape at
different value functions `J`). -/
def Dstar (M : MarkovDecisionModel E A) (Jval : E → EReal) (x : E) : Set A :=
  {a | a ∈ M.Dx x ∧ ∀ a' ∈ M.Dx x, L M Jval (x, a') ≤ L M Jval (x, a)}

end MDPFinance.Contracting
