import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn

open Filter Topology

namespace LeblSCV.BallPolydisc

/-- Lemma 1.4.7 (Lebl, p. 34). For bounded domains `U ⊆ ℝⁿ`, `V ⊆ ℝᵐ` and a continuous
`f : U → V`, `f` is proper iff for every sequence `p_k` in `U` converging to a point of `∂U`,
every limit point of `f(p_k)` lies in `∂V`. -/
theorem proper_iff_cluster_points_in_frontier {n m : ℕ}
    (U : Set (Fin n → ℝ)) (V : Set (Fin m → ℝ))
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (hfUV : Set.MapsTo f U V) (hf : ContinuousOn f U) :
    IsProperMapOn f U V ↔
      ∀ (p : ℕ → (Fin n → ℝ)) (x : Fin n → ℝ), (∀ k, p k ∈ U) →
        Tendsto p atTop (𝓝 x) → x ∈ frontier U →
          ∀ q : Fin m → ℝ, MapClusterPt q atTop (fun k => f (p k)) → q ∈ frontier V := by sorry

end LeblSCV.BallPolydisc
