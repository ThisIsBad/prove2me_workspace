import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.13, Dai & Harrison p. 200 (PDF p. 216): for each `t > 0`, the upper-right Dini
derivative of `withinGroupEntropy` (Eq. 10.50) is bounded by, for each class `i` with `Z_i(t) > 0`,
the sum of the upper-left Dini derivative of `Z_i` times `log(Z_i(t)/Y_{grp i}(t))`, plus the
upper-right Dini derivative of `Z_i`, minus the upper-left Dini derivative of `Y_{grp i}` times
`Z_i(t)/Y_{grp i}(t)` (Eq. 10.56) — summed over all classes `i`, which is equivalent to the book's
double sum over groups `ℓ` then classes `i ∈ I(ℓ)`, since every class belongs to exactly one
group. `Z` is Lipschitz on `[0, ∞)` (as every fluid model solution is, Section 10.5), so that
all the Dini derivatives involved are finite. -/
theorem within_group_entropy_dini_bound
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t) :
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ∑ i, if Zh t i = 0 then (0 : EReal) else
        diniUpperLeft (fun s => Zh s i) t *
            ((Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) : EReal) +
          diniUpperRight (fun s => Zh s i) t -
            diniUpperLeft (fun s => groupAggregate grp (Zh s) (grp i)) t *
              ((Zh t i / groupAggregate grp (Zh t) (grp i) : ℝ) : EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
