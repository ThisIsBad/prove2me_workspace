import Definitions.Def_GeneralCK_statement


namespace GeneralCK
open scoped BigOperators

/-- Lower entropy inverse specified by its sublevel threshold.
Its inverse laws are proved in `ProfileBasics` and `EtaMonotone`. -/
noncomputable def entropyInverse (h : ℝ) : ℝ :=
  sInf {v : ℝ | 0 ≤ v ∧ v ≤ 1 / 2 ∧ h ≤ H v}

noncomputable def J (v : ℝ) : ℝ := Real.log ((1 - v) / v) / Real.log 2

noncomputable def eta (h : ℝ) : ℝ :=
  if h = 1 then 0 else (1 - 2 * entropyInverse h) * J (entropyInverse h)

/-- Only the positive `z,h` branch is used for nonzero contacts.
The cap contact is proved in `ProfileBasics`; general contact laws and calculus
are proved in `RadialContact` and `RadialDerivatives`. -/
noncomputable def radialContact (z h : ℝ) : ℝ :=
  sInf {v : ℝ | 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v)}

noncomputable def F (z h : ℝ) : ℝ :=
  if z = 0 then 0 else z * J (radialContact z h)

noncomputable def phi (m h : ℝ) : ℝ := eta h - F |1 - 2 * m| h
noncomputable def psi (m h : ℝ) : ℝ := eta (h + 1 - H m)
noncomputable def B (m h : ℝ) : ℝ := max (phi m h) (psi m h)

/-- Interior edge cost only. No claim about its totalized boundary values. -/
noncomputable def interiorCost (u v : ℝ) : ℝ := (v - u) * (J u - J v) / 2

/-- The finite, interior-law consequence of manuscript Theorem 1.1 needed
by static cube induction. There is no pointwise order assumption on `u,v`.
This proposition is not assumed globally and has not been proved. -/
def FiniteHybridBellman : Prop :=
  ∀ (k : ℕ) (w u v : Fin k → ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    (∀ i, 0 < u i ∧ u i < 1) → (∀ i, 0 < v i ∧ v i < 1) →
    let a := ∑ i, w i * u i
    let b := ∑ i, w i * v i
    let e := ∑ i, w i * H (u i)
    let f := ∑ i, w i * H (v i)
    B ((a + b) / 2) ((e + f) / 2) ≤
      (B a e + B b f) / 2 + ∑ i, w i * interiorCost (u i) (v i)

/-- The conditional transfer proposition. Proved by `bellmanToCK` in `ConditionalCK`. -/
def BellmanToCK : Prop := FiniteHybridBellman → GeneralCourtadeKumar

end GeneralCK
