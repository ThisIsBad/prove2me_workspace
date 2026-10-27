import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_34 (n : ℝ) (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) :
    let P : Matrix (Fin k) (Fin k) ℝ := fun s t => if t = finRotate k s then 1 else 0
    let G : Matrix (Fin k) (Fin k) ℝ := P - 1
    let A : Matrix (Fin k) (Fin k) ℝ := Pᵀ - P
    let C : Matrix (Fin k) (Fin k) ℝ := (1 / n) • (1 : Matrix (Fin k) (Fin k) ℝ) + (1 / 2 : ℝ) • A
    (1 / n ^ k) / (C + (1 / 2 : ℝ) • (Gᵀ * G)).det = 1 / ((n + 1) ^ k - n ^ k) := by sorry

end GaussAddit.Noise

