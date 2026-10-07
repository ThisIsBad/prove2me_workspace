import Mathlib
import Definitions.Def_WilliamsonShmoys_ParallelMakespan

namespace GrahamAnomaly.KLongest

/-- Load of processor `p` after the first `k` jobs in the priority list. -/
noncomputable def loadBefore {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) (p : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < k ∧ σ j = p), μ j

/-- Each successive job is assigned to a processor with minimum current load. -/
def IsListAssignment {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) : Prop :=
  ∀ j : Fin r, ∀ p : Fin n,
    loadBefore μ L σ (L.symm j) (σ j) ≤ loadBefore μ L σ (L.symm j) p

/-- The latest completion time among the first `k` jobs of the list. -/
noncomputable def prefixFinish {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.sup' h (loadBefore μ L σ k)
  else 0

/-- Least makespan among all assignments of the jobs to the processors. -/
noncomputable def optFinish {r : ℕ} (μ : Fin r → ℝ) (n : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin r → Fin n)).Nonempty then
    Finset.univ.inf' h (WilliamsonShmoys.makespan μ)
  else 0

/-- Length of the longest job after the first `k` positions; zero if none remain. -/
noncomputable def alphaStar {r : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (k : ℕ) : ℝ :=
  if h : (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).Nonempty then
    (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).sup' h μ
  else 0

end GrahamAnomaly.KLongest
