import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- (vi)–(viii) of p. 704, with a fixed choice `J = (J¹, …, Jᵈ)` of the stochastic integrals:
`Y`, `Z`, `K` are `𝓕`-progressively measurable; each `Jʲ` is the Itô integral process
`Jʲ_t = ∫₀ᵗ Zʲ_s dBʲ_s` (`Peng1990.SMP.IsItoIntegral`, which requires `Zʲ ∈ ℍ²`); and almost
surely, simultaneously for all `t ∈ [0, T]`:
* every `Jʲ` has continuous paths on `[0, T]` and `s ↦ f(s, Y_s, Z_s)` is integrable on `[0, T]`;
* (vi) `Y_t = ξ + ∫ₜᵀ f(s, Y_s, Z_s) ds + K_T − K_t − ∫ₜᵀ (Z_s, dB_s)`, where
  `∫ₜᵀ (Z_s, dB_s) = Σⱼ (Jʲ_T − Jʲ_t)`;
* (vii) `Y_t ≥ S_t`;
* (viii) `K` is continuous and nondecreasing on `[0, T]`, `K_0 = 0`, and
  `∫₀ᵀ (Y_t − S_t) dK_t = 0`, the integral being taken against the Stieltjes measure of the path
  `t ↦ K_{t ∧ T}`. -/
def SolvesRBSDEWith {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 Y ∧ IsStronglyProgressive 𝓕 Z ∧ IsStronglyProgressive 𝓕 K ∧
    (∀ j, IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => Z s ω j) (J j)) ∧
    ∀ᵐ ω ∂P,
      (∀ j, ContinuousOn (fun t => J j t ω) (Iic T)) ∧
      IntegrableOn (fun s : ℝ => f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
        (Icc 0 (T : ℝ)) ∧
      (∀ t ≤ T, Y t ω = ξ ω
          + ∫ s in Icc (t : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
          + K T ω - K t ω - ∑ j, (J j T ω - J j t ω)) ∧
      (∀ t ≤ T, S t ω ≤ Y t ω) ∧
      Monotone (fun t => K (min t T) ω) ∧ Continuous (fun t => K (min t T) ω) ∧ K 0 ω = 0 ∧
      ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Y t.toNNReal ω - S t.toNNReal ω)
        ∂(pathMeasure fun t => K (min t T) ω) = 0

/-- `(Y, Z, K)` satisfies (vi)–(viii) of p. 704 for some choice of the stochastic integrals
`∫₀ᵗ Zʲ dBʲ` (see `SolvesRBSDEWith`). -/
def SolvesRBSDE {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ) :
    Prop :=
  ∃ J : Fin d → ℝ≥0 → Ω → ℝ, SolvesRBSDEWith 𝓕 P T B ξ f S Y Z K J

/-- (v): `Z ∈ ℍ²`, i.e. `Z` is progressively measurable with `E ∫₀ᵀ |Z_t|² dt < ∞`. -/
def SatisfiesV {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  L2F 𝓕 P T Z

/-- (v′): `Y ∈ 𝒮²` and `K_T ∈ 𝕃²`. -/
def SatisfiesVPrime (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Y K : ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2 𝓕 P T Y ∧ ∫⁻ ω, ‖K T ω‖ₑ ^ 2 ∂P < ⊤

/-- Two triples `(Y, Z, K)` and `(Y', Z', K')` are equal as solutions on `[0, T]`: `Y, Y'` and
`K, K'` are indistinguishable on `[0, T]` (almost surely `Y_t = Y'_t` and `K_t = K'_t` for all
`t ∈ [0, T]`), and `Z = Z'` `dP ⊗ dt`-almost everywhere on `Ω × [0, T]`, i.e.
`E ∫₀ᵀ |Z_t − Z'_t|² dt = 0`. -/
def SameSolution {d : ℕ} (P : Measure Ω) (T : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ) (Y' : ℝ≥0 → Ω → ℝ)
    (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ T, Y t ω = Y' t ω ∧ K t ω = K' t ω) ∧
    ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)) ∂volume ∂P = 0

end ReflectedBSDE.Existence
