import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.14, Dai & Harrison p. 203 (PDF p. 219): at each regular point `t > 0` of `Z`, the
upper-right Dini derivative of `withinGroupEntropy` is bounded by
`∑_i Ż_i(t) log(Z_i(t)/Y_{grp i}(t))` over classes `i` with `Z_i(t) > 0` (Eq. 10.66). -/
theorem within_group_entropy_dini_bound_regular
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t)
    (hreg : ∀ i, DifferentiableAt ℝ (fun s => Zh s i) t) :
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ((∑ i, if Zh t i = 0 then 0 else
        deriv (fun s => Zh s i) t * Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) :
          EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
