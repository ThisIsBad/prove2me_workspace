import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory FragLOB.Collapse

theorem solution {N : ℕ} (M : Market N) (hM : M.Standing) (Q : Fin N → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) (hW : 0 < workload M Q) :
    ∀ i, delay M Q i = workload M Q / (M.mu * M.beta i) := by
  intro i
  obtain ⟨-, -, hmu, hb⟩ := hM
  have hbi := hb i
  unfold delay
  split_ifs with h
  · unfold marketRate
    have hne : workload M Q ≠ 0 := hW.ne'
    field_simp
  · rfl
