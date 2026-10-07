import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process
import Definitions.Def_KingmanSubadditive_BanachAlgebra_RandomProduct

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **Proof of Theorem 6, §2.3, p. 893** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "If `x_st = log ‖Y_{s+1} Y_{s+2} ⋯ Y_t‖`,
then (2.3.2) implies that `x = (x_st)` satisfies S₁, S₂ and S₃′." Here `(Y_n)_{n≥1}` is a
stationary sequence in a real or complex Banach algebra `𝔅` with `E{(log ‖Y₁‖)⁺} < ∞` (the
hypotheses of Theorem 6), and (2.3.2) is `‖AB‖ ≤ ‖A‖ ‖B‖`.

The conclusion lists: every `x_st` (`s < t`) is measurable; S₁ holds for every `ω` (in `EReal`);
S₂ holds (equality of the laws of the shifted and unshifted paths on `Interval → EReal`); and
S₃′ holds in the form `E(x₀₁⁺) < ∞`.

**Formalization Note.** `x_st` takes values in `[−∞, ∞)`: `log ‖0‖ = −∞` (`ENNReal.log 0 = ⊥`),
so the process is `EReal`-valued and S₁ is read with `−∞ + a = −∞`. The paper's Theorem 2 is
stated for real random variables; the paper applies it to this process without comment. Each
`Y_n` is strongly measurable (separably valued), which makes the products measurable without
assuming `𝔅` separable. `𝔅` is a unital `NormedRing` (`‖AB‖ ≤ ‖A‖‖B‖` is part of the structure)
that is complete and a normed algebra over `𝕜 = ℝ` or `ℂ` (`RCLike`). -/
theorem logNormProcess_conditions {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    IsMeasurableFamily (logNormProcess Y) ∧
      (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
        logNormProcess Y s u ω ≤ logNormProcess Y s t ω + logNormProcess Y t u ω) ∧
      S2 P (logNormProcess Y) ∧
      ∫⁻ ω, (logNormProcess Y 0 1 ω).toENNReal ∂P < ⊤ := by sorry

end KingmanSubadditive.BanachAlgebra

