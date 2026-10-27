import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 15 (Properties of Graph G under Event G), p. 57, pathwise: on every trajectory in the
good event, for products `j < i` (paper: `i > j`, so `μ_j > μ_i`) and every level `ℓ ≥ ℓ⋆`
(Lean: `F ≤ 2^(k+1)`), (1) `G^(ℓ)` never holds the incorrect edge `(j, i)`, and (2) once
`η̂^(ℓ)_{i,t}, η̂^(ℓ)_{j,t} ≥ γ_{j,i}` at the end of round `t`, `G^(ℓ)` holds the edge `(i, j)` at the
end of every round `t' ≥ t`. -/
theorem lemma_15 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (hG : goodEvent inst F tb fb τ)
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    (∀ t : ℕ, t ≤ T → (j, i) ∉ (stateAt tb fb τ t).graph k) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ T →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k i →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k j →
      ∀ t' : ℕ, t ≤ t' → t' ≤ T → (i, j) ∈ (stateAt tb fb τ t').graph k) := by sorry

end FakeUserRanking.FORC

