import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.LinearSuprema

noncomputable def coeffNorm {N : ℕ} (α : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, α i ^ 2)

noncomputable def sigma {N : ℕ} (F : Set (Fin N → ℝ)) : ℝ :=
  sSup (coeffNorm '' F)

noncomputable def linearSupremum {N : ℕ} (F : Set (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  sSup ((fun α : Fin N → ℝ => ∑ i, α i * x i) '' F)

def mismatchVectors {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧
    ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

def mismatchHull {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  convexHull ℝ (mismatchVectors A x)

noncomputable def convexDistance {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ENNReal :=
  ⨅ s ∈ mismatchHull A x,
    ENNReal.ofReal (Real.sqrt (∑ i, s i ^ 2))

def linearSublevel {N : ℕ} (F : Set (Fin N → ℝ))
    (r : Fin N → ℝ) (a : ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    linearSupremum F (fun i => r i + x i) ≤ a}

end TalagrandConc.LinearSuprema
