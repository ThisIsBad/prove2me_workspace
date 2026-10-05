import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal
open Filter Topology

namespace SennottDP.ContinuousTime

/-- Theorem 10.3.3 (p. 246). -/
theorem asm_optimal_ctmdc {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i := by sorry

end SennottDP.ContinuousTime

