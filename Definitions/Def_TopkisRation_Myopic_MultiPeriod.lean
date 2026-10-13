import Definitions.Def_TopkisRation_Myopic_Model

namespace TopkisRation.Myopic

open MeasureTheory Filter Topology

variable {n : ℕ}

/-- The §3 multiperiod model. The salvage and ordering costs in `P` are replaced below. -/
structure MultiModel (n : ℕ) where
  N : ℕ
  P : ℕ → Model n
  c : ℕ → ℝ
  v : ℝ

/-- The §1 model with replacement terminal costs. -/
def Model.withSalvage (M : Model n) (v₁ v₂ : ℝ → ℝ) : Model n :=
  { M with v₁ := v₁, v₂ := v₂ }

/-- `Crev r = C_{N+1-r}`; the successor case is recursion (19). -/
noncomputable def MultiModel.Crev (Q : MultiModel n) : ℕ → ℝ → ℝ
  | 0 => fun w => (Q.c (Q.N + 1) - Q.v) * max w 0
  | r + 1 => fun w =>
      let m := Q.N - r
      sInf ((fun z => Q.c m * z +
        ((Q.P m).withSalvage (fun _ => 0)
          (fun y => -Q.c (m + 1) * y + Q.Crev r y)).g (Q.P m).k z 0)
        '' Set.Ici (max w 0))

/-- The value `Cₘ` for `1 ≤ m ≤ N+1`. -/
noncomputable def MultiModel.C (Q : MultiModel n) (m : ℕ) : ℝ → ℝ :=
  Q.Crev (Q.N + 1 - m)

/-- Actual period cost `g̃ᵐ` with continuation value `Cₘ₊₁`. -/
noncomputable def MultiModel.gtilde (Q : MultiModel n) (m : ℕ) (z : ℝ) : ℝ :=
  Q.c m * z + ((Q.P m).withSalvage (fun _ => 0)
    (fun y => -Q.c (m + 1) * y + Q.C (m + 1) y)).g (Q.P m).k z 0

/-- The single-period cost `gᵐ`, with linear terminal cost. -/
noncomputable def MultiModel.gmyopic (Q : MultiModel n) (m : ℕ) (z : ℝ) : ℝ :=
  Q.c m * z + ((Q.P m).withSalvage (fun _ => 0)
    (fun y => -Q.c (m + 1) * y)).g (Q.P m).k z 0

/-- A myopic level is any minimum of `gᵐ` on the nonnegative half-line, or infinity if none exists. -/
def IsMyopicLevel (φ : ℝ → ℝ) (y : WithTop ℝ) : Prop :=
  (y = ⊤ ∧ ¬ ∃ x, 0 ≤ x ∧ ∀ z, 0 ≤ z → φ x ≤ φ z) ∨
  ∃ x : ℝ, y = x ∧ 0 ≤ x ∧ ∀ z, 0 ≤ z → φ x ≤ φ z

/-- Standing assumptions of §3, including (D′). -/
structure MultiModel.Standing (Q : MultiModel n) : Prop where
  n_pos : 0 < n
  N_pos : 0 < Q.N
  k_pos : ∀ m ∈ Finset.Icc 1 Q.N, 0 < (Q.P m).k
  period : ∀ m ∈ Finset.Icc 1 Q.N,
    ((Q.P m).withSalvage (fun _ => 0) (fun y => -Q.c (m + 1) * y)).Standing
  a01 : ∀ m ∈ Finset.Icc 1 Q.N, ∀ t ∈ Finset.Icc 1 (Q.P m).k,
    (Q.P m).a t = 0 ∨ (Q.P m).a t = 1
  c_last : 0 ≤ Q.c (Q.N + 1)
  v_le : Q.v ≤ Q.c (Q.N + 1)
  D' : ∀ m ∈ Finset.Icc 1 Q.N, ∃ η : ℝ, 0 < η ∧ ∀ᶠ w in atTop, (η : EReal) ≤
    TopkisRation.Levels.rightDeriv (fun w => Q.c m * w +
      (∑ i ∈ Finset.Icc m Q.N, ∑ t ∈ Finset.Icc 1 (Q.P i).k, (Q.P i).h t w) -
      Q.v * w) w

end TopkisRation.Myopic
