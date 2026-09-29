import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

theorem prop_2_2_1 (φ : Formula5) (τ : Fin φ.n → Bool)
    (hτ : ∀ τ' : Fin φ.n → Bool,
      (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ' (φ.var c p)))).card ≤
        (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card)
    (ε : ℝ)
    (hε : ε = 1 - ((Finset.univ.filter
      (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card : ℝ) / φ.M) :
    (∃ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ = 1 - ε / 3) ∧
      ∀ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ ≤ 1 - ε / 3 := by sorry

end SetCoverThreshold.SetCover
