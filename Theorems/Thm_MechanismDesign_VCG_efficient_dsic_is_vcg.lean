import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Corollary 7.1 (p.134), Green–Laffont (1977) and Holmström (1979), with continuity
added (see the natural-language statement): each type set `Θᵢ = Sᵢ` is a convex subset of the
Euclidean space `ℝ^{dᵢ}` and each `uᵢ(a, ·)` is convex and continuous on `Sᵢ`. Every dominant
strategy incentive-compatible mechanism `(q, t₁, …, t_N)` with an efficient decision rule `q`
is a VCG mechanism: `tᵢ(θ) = −∑_{j ≠ i} u_j(q(θ), θ_j) + τᵢ(θ₋ᵢ)` for some `τᵢ : Θ₋ᵢ → ℝ`. -/
theorem efficient_dsic_is_vcg {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (heff : IsEfficient (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M.q) :
    IsVCG (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M := by sorry

end MechanismDesign.VCG

