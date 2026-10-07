import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem theorem_6_hamiltonian_iff {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1)))
    (hΓ : Monotone Γ) (hΓn : Γ (Fin.last n) = Finset.univ) (φ : Equiv.Perm (Fin (n + 1)))
    (hφ : ∀ i, ∃ j : ℕ,
      Γ i = (Finset.univ.filter (fun k : Fin (n + 1) => (k : ℕ) < j)).map φ.toEmbedding) :
    (∃ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ ∧ ∀ i, ψ i ∈ Γ i) ↔
      (∀ q, φ q ∈ Γ q) ∧ (Gprime Γ φ).Connected := by sorry

end GilmoreGomoryTSP.Bottleneck

