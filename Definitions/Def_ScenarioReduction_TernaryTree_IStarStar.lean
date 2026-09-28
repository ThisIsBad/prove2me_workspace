import Mathlib

namespace ScenarioReduction.TernaryTree

/-- Scenario `σ` takes the middle branch (increment `0`) at paper level `l` (`1 ≤ l ≤ K`). -/
def IsMid {K : ℕ} (σ : Fin K → Fin 3) (l : ℕ) : Prop :=
  ∃ r : Fin K, r.val + 1 = l ∧ σ r = 1

/-- Scenario `σ` takes an outer branch (increment `±δ^l`) at paper level `l` (`1 ≤ l ≤ K`). -/
def IsOuter {K : ℕ} (σ : Fin K → Fin 3) (l : ℕ) : Prop :=
  ∃ r : Fin K, r.val + 1 = l ∧ σ r ≠ 1

/-- The index set `I_**` of the proof of Proposition 3.2 of Heitsch–Römisch (2003), stated by
branch indices: the middle branch at level `k0` and outer branches at levels `k0+1`, `k0+2`, or an
outer branch at level `k0` and middle branches at levels `k0+1`, `k0+2`. -/
noncomputable def IStarStar (K k0 : ℕ) : Finset (Fin K → Fin 3) := by
  classical
  exact Finset.univ.filter (fun σ =>
    (IsMid σ k0 ∧ IsOuter σ (k0 + 1) ∧ IsOuter σ (k0 + 2)) ∨
    (IsOuter σ k0 ∧ IsMid σ (k0 + 1) ∧ IsMid σ (k0 + 2)))

end ScenarioReduction.TernaryTree
