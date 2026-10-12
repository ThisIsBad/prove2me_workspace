import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_DRi
open MeasureTheory

namespace GoldieRenewal.Implicit

/-- **Lemma 9.2** (Goldie 1991, Ann. Appl. Probab. 1(1), p. 143). If `f ∈ L¹(ℝ)`, then `f̌` is dRi,
where `f̌(t) := ∫_{−∞}^t e^{−(t−u)} f(u) du` (p. 128).

**Formalization Note** `f̌` is `smooth f`; dRi is `IsDRi` (Feller's definition). For `f ∈ L¹(ℝ)` the
integral defining `f̌(t)` converges absolutely for every `t`. -/
theorem lemma_9_2 (f : ℝ → ℝ) (hf : Integrable f) : IsDRi (smooth f) := by sorry

end GoldieRenewal.Implicit

