import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

namespace VapnikChervonenkis.Entropy

open MeasureTheory

/-- The **entropy** `H^S(l) = E log₂ Δ^S(x_1, …, x_l)` of the system of events `S` in samples of
size `l` (Vapnik and Chervonenkis 1971, p. 273, Subsection 6): the expectation, under the
product law `P^l` of an independent sample of size `l`, of the binary logarithm of the index.
The index takes values in `{0, 1, …, 2^l}`; `Real.logb 2 0 = 0` (the value `0` occurs only when
`S = ∅`). The paper assumes the index is measurable (p. 273); under that assumption the integrand
is bounded and measurable, so the Bochner integral is the genuine expectation. -/
noncomputable def entropy {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    (l : ℕ) : ℝ :=
  ∫ x, Real.logb 2 (Shared.index S x : ℝ) ∂(Measure.pi fun _ : Fin l => P)

end VapnikChervonenkis.Entropy
