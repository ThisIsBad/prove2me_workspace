import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.1 (pp.131–132), Rochet's theorem for dominant strategies: a decision
rule `q` is part of a dominant strategy incentive-compatible direct mechanism if and only if, for
every agent `i`, every `θ₋ᵢ`, and every sequence of types `θ¹ᵢ, …, θᵏᵢ` of agent `i` with
`θᵏᵢ = θ¹ᵢ`, `∑_{κ=1}^{k-1} (uᵢ(aᵏ, θᵏ⁺¹ᵢ) − uᵢ(aᵏ, θᵏᵢ)) ≤ 0` where `aᵏ = q(θᵏᵢ, θ₋ᵢ)`.
The sequence is `θs : Fin (k + 1) → Θ i` (indices `0, …, k`), and `θ₋ᵢ` is the part of the
profile `θ` other than coordinate `i`. -/
theorem dsic_iff_cyclically_monotone {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j) (k : ℕ) (θs : Fin (k + 1) → Θ i), θs (Fin.last k) = θs 0 →
        ∑ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ 0 := by sorry

end MechanismDesign.VCG

