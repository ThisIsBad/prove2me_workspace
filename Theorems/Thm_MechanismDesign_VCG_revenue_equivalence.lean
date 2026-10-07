import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.3 (p.132), after Krishna and Maenner (2001), with continuity added
(see the natural-language statement): each type set `Θᵢ = Sᵢ` is a convex subset of the
Euclidean space `ℝ^{dᵢ}` and each `uᵢ(a, ·)` is convex and continuous on `Sᵢ`. If
`(q, t₁, …, t_N)` is dominant strategy incentive-compatible, then `(q, t'₁, …, t'_N)` is dominant
strategy incentive-compatible if and only if for every `i` there is `τᵢ : Θ₋ᵢ → ℝ` with
`t'ᵢ(θ) = tᵢ(θ) + τᵢ(θ₋ᵢ)` for all `θ ∈ Θ`. -/
theorem revenue_equivalence {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (t' : ι → (∀ i, ↥(S i)) → ℝ) :
    DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, t'⟩ ↔
      ∀ i : ι, ∃ τ : Others (fun i => ↥(S i)) i → ℝ,
        ∀ θ : ∀ j, ↥(S j), t' i θ = M.t i θ + τ (restrict θ i) := by sorry

end MechanismDesign.VCG

