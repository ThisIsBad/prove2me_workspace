import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open MeasureTheory ProbabilityTheory Matrix Filter Topology
theorem asymptotic_linearity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (d : ℕ → ℕ) (L : (n : ℕ) → Ω → (Fin (d n) → ℝ) → ℝ) (f : (n : ℕ) → (Fin (d n) → ℝ) → ℝ)
    (thetaStar : (n : ℕ) → Fin (d n) → ℝ) (thetaHat : (n : ℕ) → Ω → Fin (d n) → ℝ)
    (OmegaHat : (n : ℕ) → Ω → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (OmegaStar : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (r1 r2 r3 r4 r5 : ℕ → ℝ) (K c1 c2 c3 L1 L2 : ℝ) (E : ℕ → Set Ω)
    (i j : (n : ℕ) → Fin (d n)) (hij : ∀ n, i n ≠ j n)
    (hA : Assumptions P d L f thetaStar thetaHat OmegaHat OmegaStar
      r1 r2 r3 r4 r5 K c1 c2 c3 L1 L2 E)
    (hr1 : Tendsto r1 atTop (𝓝 0)) (hr4 : Tendsto r4 atTop (𝓝 0))
    (hscale : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (r1 n ^ 2 * r5 n + (r1 n + r4 n) * (r1 n ^ 2 + r2 n) + r1 n * r3 n)) atTop (𝓝 0))
    (hvar : ∃ C : ℝ, 0 < C ∧ ∀ n,
      C ≤ popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n) ∧
      C ≤ popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) =>
        Real.sqrt (n : ℝ) *
          (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n))
          / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n))
        + Real.sqrt (n : ℝ) *
          (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n)
          / Real.sqrt (popVar P (L n) (f n) (OmegaStar n) (thetaStar n) (j n))) atTop 0 ∧
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) =>
        Real.sqrt (n : ℝ) *
          ((estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (i n) - thetaStar n (i n))
            - (estThetaD (L n ω) (f n) (OmegaHat n ω) (thetaHat n ω) (j n) - thetaStar n (j n)))
          / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n))
        + Real.sqrt (n : ℝ) *
          ((thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (i n)
            - (thetaStar11 (f n) (OmegaStar n) (thetaStar n) *ᵥ grad (L n ω) (thetaStar n)) (j n))
          / Real.sqrt (popVarPair P (L n) (f n) (OmegaStar n) (thetaStar n) (i n) (j n)))
      atTop 0 := by sorry
end LagrangeRank.Debias

