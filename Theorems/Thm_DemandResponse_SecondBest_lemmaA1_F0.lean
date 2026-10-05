import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Lemma A.1 (arXiv:1810.09063v3, p. 29): `F₀(q) = f₀(q, -q) = -2 H_v(-q)`, and `F₀` is
non-decreasing. Stated for every real `q`. -/
theorem lemmaA1_F0 {N d : ℕ} (P : Params N d) :
    (∀ q : ℝ, F0 P q = f0 P q (-q) ∧ f0 P q (-q) = -2 * Hv P (-q)) ∧ Monotone (F0 P) := by sorry

end DemandResponse.SecondBest

