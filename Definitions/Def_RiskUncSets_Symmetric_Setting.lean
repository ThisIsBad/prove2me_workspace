import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fin.Tuple.Sort
noncomputable section

namespace RiskUncSets.Symmetric

/-- Definition 4.6: probability weights in decreasing order. -/
def restrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin N) ∧ Antitone q}

/-- Definition 4.7: the convex hull of all weighted permutations of the data. -/
def permutohull {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i)

/-- The sample mean `A e_N` of the data. -/
def sampleMean {N n : ℕ} (a : Fin N → Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (1 / (N : ℝ)) • a i

/-- Definition 4.8: symmetry about a point belonging to the set. -/
def CentrallySymmetric {n : ℕ} (P : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) : Prop :=
  x₀ ∈ P ∧ ∀ x, x₀ + x ∈ P → x₀ - x ∈ P

/-- Definition 4.9 and equation (9). -/
def symRestrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ restrictedSimplex N ∧
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i)}

/-- Equation (4): the reward-sign distortion risk measure for ordered observations. -/
def muQ {N : ℕ} (q X : Fin N → ℝ) : ℝ :=
  -∑ i, q i * X (Tuple.sort X i)

/-- The number of symmetric generators in Theorem 4.4. -/
def Nhat (N : ℕ) : ℕ := N / 2 + 1

/-- Equation (10), with both the observation and generator indices starting at zero. -/
def qbar {N : ℕ} (j : Fin (Nhat N)) : Fin N → ℝ :=
  fun i =>
    if (i : ℕ) < (j : ℕ) then 2 / (N : ℝ)
    else if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) + (j : ℕ) + 1 ≤ N then 1 / (N : ℝ)
    else 0

end RiskUncSets.Symmetric
