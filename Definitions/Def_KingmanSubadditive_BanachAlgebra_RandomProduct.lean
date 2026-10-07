import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- A **stationary sequence** `(Y_n)_{n ≥ 1}` of random elements of `𝔅` (Kingman, *Subadditive
ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, §2.3, p. 893,
Theorem 6): the law of the shifted sequence `(Y_{n+1})_{n≥1}` on the product σ-algebra of
`ℕ → 𝔅` equals the law of `(Y_n)_{n≥1}`.

**Formalization Note.** The sequence is indexed by `n ≥ 1`; `Y 0` is never used. Coordinate `k`
of the sequence path is `Y (k+1)`, of the shifted path `Y (k+2)`. Stationarity is joint-law
invariance, not equality of one-dimensional distributions. -/
def IsStationarySeq {Ω 𝔅 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔅] (P : Measure Ω)
    (Y : ℕ → Ω → 𝔅) : Prop :=
  Measure.map (fun ω (k : ℕ) => Y (k + 2) ω) P = Measure.map (fun ω (k : ℕ) => Y (k + 1) ω) P

/-- The ordered product `Y_{s+1} Y_{s+2} ⋯ Y_t` (left to right; `𝔅` is not commutative), as in
the proof of Theorem 6, p. 893. For `s < t` the list `[s+1, …, t]` has `t − s` entries. -/
def prodRange {Ω 𝔅 : Type*} [Monoid 𝔅] (Y : ℕ → Ω → 𝔅) (s t : ℕ) (ω : Ω) : 𝔅 :=
  ((List.range' (s + 1) (t - s)).map (fun i => Y i ω)).prod

/-- `log ‖a‖ ∈ [−∞, ∞)` as an extended real, with `log ‖0‖ = −∞`. -/
noncomputable def logNorm {𝔅 : Type*} [Norm 𝔅] (a : 𝔅) : EReal :=
  ENNReal.log (ENNReal.ofReal ‖a‖)

/-- The log-norm process of the proof of Theorem 6, p. 893:
`x_st = log ‖Y_{s+1} Y_{s+2} ⋯ Y_t‖`, an `EReal`-valued two-parameter family. -/
noncomputable def logNormProcess {Ω 𝔅 : Type*} [Monoid 𝔅] [Norm 𝔅] (Y : ℕ → Ω → 𝔅) :
    ℕ → ℕ → Ω → EReal :=
  fun s t ω => logNorm (prodRange Y s t ω)

end KingmanSubadditive.BanachAlgebra
