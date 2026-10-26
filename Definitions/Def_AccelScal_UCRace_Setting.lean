import Mathlib
import Definitions.Def_AccelScal_UCRace_ExponentialRace
import Definitions.Def_AccelScal_UCMonopoly_Setting

noncomputable section

open MeasureTheory

namespace AccelScal.UCRace

structure Tech where
  A : ℝ
  β : ℝ
  η : ℝ
  γ : ℝ

def Tech.Standing (T : Tech) : Prop :=
  0 < T.A ∧ 0 < T.η ∧ 0 ≤ T.β ∧ T.β < 1 ∧
    0 ≤ T.γ ∧ T.γ < 1 ∧ T.β + T.γ < 1 ∧ 1 < T.A * T.η

def Tech.u (T : Tech) (R : ℝ) : ℝ := T.A * R ^ T.β

def Tech.lam (T : Tech) (R : ℝ) : ℝ := T.η * R ^ T.γ

def Tech.Rbar (T : Tech) : ℝ :=
  (T.A * T.η) ^ (1 / (1 - (T.β + T.γ)))

/-- Firm 1 receives its mean payoff if its discovery time is first, and pays until
the first discovery. -/
def payoff1 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    (Real.exp (-r * p.1) * T1.u R1 * (if p.1 < p.2 then 1 else 0)
      - R1 * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t))
      ∂exponentialRace (T1.lam R1) (T2.lam R2)

/-- Firm 2 wins when the second coordinate is the earlier discovery time. -/
def payoff2 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    (Real.exp (-r * p.2) * T2.u R2 * (if p.2 < p.1 then 1 else 0)
      - R2 * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t))
      ∂exponentialRace (T1.lam R1) (T2.lam R2)

def BR1 (T1 T2 : Tech) (r R2 : ℝ) : Set ℝ :=
  {R1 | R1 ∈ Set.Icc 1 T1.Rbar ∧
    ∀ R1' ∈ Set.Icc 1 T1.Rbar, payoff1 T1 T2 r R1' R2 ≤ payoff1 T1 T2 r R1 R2}

def BR2 (T1 T2 : Tech) (r R1 : ℝ) : Set ℝ :=
  {R2 | R2 ∈ Set.Icc 1 T2.Rbar ∧
    ∀ R2' ∈ Set.Icc 1 T2.Rbar, payoff2 T1 T2 r R1 R2' ≤ payoff2 T1 T2 r R1 R2}

def IsNash (T1 T2 : Tech) (r R1 R2 : ℝ) : Prop :=
  R1 ∈ BR1 T1 T2 r R2 ∧ R2 ∈ BR2 T1 T2 r R1

def V1 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  (T1.u R1 * T1.lam R1 - R1) / (r + T1.lam R1 + T2.lam R2)

end AccelScal.UCRace
