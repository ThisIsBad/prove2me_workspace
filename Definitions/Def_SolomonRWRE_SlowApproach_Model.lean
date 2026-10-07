import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

namespace SolomonRWRE.SlowApproach

/-- Solomon, §2, pp. 10–11. The two-value i.i.d. environment with one-way mirrors. -/
def IsMirrorEnvironment {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (γ θ : ℝ) : Prop :=
  SolomonRWRE.Recurrence.IsRWRE P α X ∧ 1 < θ ∧ 0 < γ ∧ γ < 1 ∧ 1 ≤ γ * θ ∧
  P {ω | α 0 ω = 1} = ENNReal.ofReal (1 - γ) ∧
  P {ω | α 0 ω = (1 + θ)⁻¹} = ENNReal.ofReal γ

/-- Solomon, §1, p. 5. `T_0 = 0` and `T_j = min {k > 0 : X_k = j}`, `= ∞` if no such `k`. -/
noncomputable def passage {Ω : Type*} (X : ℕ → Ω → ℤ) (j : ℕ) (ω : Ω) : ℕ∞ :=
  if j = 0 then 0 else
    sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 0 < k ∧ X k ω = (j : ℤ)})

/-- Solomon, §2, p. 11. Position of the `n`th mirror to the right of zero. The empty-set
case is assigned zero; it has probability zero in the stated i.i.d. model. -/
noncomputable def mirrorPos {Ω : Type*} (α : ℤ → Ω → ℝ) : ℕ → Ω → ℕ
  | 0, _ => 0
  | n + 1, ω => sInf {k : ℕ | mirrorPos α n ω < k ∧ α (k : ℤ) ω = 1}

/-- Solomon, §2, p. 12. The Laplace transform of the passage-time increment between mirrors. -/
noncomputable def phi {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (n : ℕ) (u : ℝ) : ℝ :=
  ∫ ω, if passage X (mirrorPos α (n + 1) ω) ω = ⊤ ∨
      passage X (mirrorPos α n ω) ω = ⊤ then (0 : ℝ)
    else Real.exp (-u * (((passage X (mirrorPos α (n + 1) ω) ω).toNat : ℝ) -
      ((passage X (mirrorPos α n ω) ω).toNat : ℝ))) ∂P

/-- Solomon, §2, pp. 13–14. The constants in (2.9) and (2.12). -/
noncomputable def nu (θ : ℝ) : ℝ := 2 * θ / (θ - 1) ^ 2
noncomputable def K (γ θ : ℝ) : ℝ := (1 - γ) / γ * nu θ
noncomputable def rho (γ θ : ℝ) : ℝ := Real.logb (1 / γ) θ

end SolomonRWRE.SlowApproach
