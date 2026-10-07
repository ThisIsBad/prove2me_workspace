import Mathlib

namespace GilmoreGomory61.CuttingStock

/-- The ordered piece lengths, demands, stock lengths, and stock costs on p. 850. -/
structure Instance (m k : ℕ) where
  ℓ : Fin m → ℝ
  N : Fin m → ℕ
  L : Fin k → ℝ
  c : Fin k → ℝ

/-- The length consumed by the pattern in (6). -/
def patLen {m k : ℕ} (I : Instance m k) (a : Fin m → ℕ) : ℝ :=
  ∑ i, I.ℓ i * (a i : ℝ)

/-- A stock length together with a nonnegative integer cutting pattern fitting that stock. -/
def Activity {m k : ℕ} (I : Instance m k) :=
  {p : Fin k × (Fin m → ℕ) // patLen I p.2 ≤ I.L p.1}

/-- Activity columns and the surplus variables of (2). -/
def Col {m k : ℕ} (I : Instance m k) := Activity I ⊕ Fin m

/-- The coefficient column in (2): activity counts or a surplus column `-eᵢ`. -/
def colVec {m k : ℕ} (I : Instance m k) : Col I → Fin m → ℝ
  | Sum.inl p => fun i => (p.1.2 i : ℝ)
  | Sum.inr i' => fun i => if i = i' then -1 else 0

/-- Cost coefficient in (1); surplus variables have zero cost. -/
def colCost {m k : ℕ} (I : Instance m k) : Col I → ℝ
  | Sum.inl p => I.c p.1.1
  | Sum.inr _ => 0

/-- The real relaxation of (2)–(3), with finitely supported column weights. -/
def Feasible {m k : ℕ} (I : Instance m k) (z : Col I →₀ ℝ) : Prop :=
  (∀ j, 0 ≤ z j) ∧
  ∀ i, (z.sum fun j v => colVec I j i * v) = (I.N i : ℝ)

/-- Objective (1) on a finitely supported solution. -/
def cost {m k : ℕ} (I : Instance m k) (z : Col I →₀ ℝ) : ℝ :=
  z.sum fun j v => colCost I j * v

end GilmoreGomory61.CuttingStock
