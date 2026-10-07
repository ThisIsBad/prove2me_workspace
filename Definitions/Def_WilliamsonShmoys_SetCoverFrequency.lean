import Mathlib.Data.Real.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
open scoped BigOperators
namespace WilliamsonShmoys


/-- A list of binary naturals with a comma after every entry, including zero.
Mathlib encodes zero as the empty bit string; the comma makes zeros and list
boundaries unambiguous. Only bit and comma symbols of its finite alphabet occur. -/
def lptEncodeNaturals (xs : List ℕ) : List Computability.Γ' :=
  xs.flatMap fun x =>
    (Computability.encodeNat x).map Computability.Γ'.bit ++ [.comma]

/-- Signed numerator and positive denominator, all binary; length first. -/
def maxsatEncodeRationals (q : List ℚ) : List Computability.Γ' :=
  lptEncodeNaturals (q.length :: q.flatMap fun r =>
    [if r.num < 0 then 1 else 0, r.num.natAbs, r.den])

def coverContaining {n m : ℕ} (sets : Fin m → Finset (Fin n))
    (i : Fin n) : Finset (Fin m) := Finset.univ.filter fun j => i ∈ sets j

def coverFeasible {n m : ℕ} (sets : Fin m → Finset (Fin n))
    (C : Finset (Fin m)) : Prop := ∀ i, ∃ j ∈ C, i ∈ sets j

noncomputable def coverCost {m : ℕ} (w : Fin m → ℝ)
    (C : Finset (Fin m)) : ℝ := ∑ j ∈ C, w j

/-- LP (1.2): no upper bound on x, including for zero-cost sets. -/
def coverLPFeasible {n m : ℕ} (sets : Fin m → Finset (Fin n))
    (x : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, 1 ≤ ∑ j ∈ coverContaining sets i, x j

noncomputable def coverLPCost {m : ℕ} (w x : Fin m → ℝ) : ℝ :=
  ∑ j, w j * x j

def coverMaxFrequency {n m : ℕ} (sets : Fin m → Finset (Fin n)) : ℕ :=
  Finset.univ.sup fun i => (coverContaining sets i).card

/-- An attained LP minimum, quantified over all real feasible vectors. -/
def IsCoverLPOptimum {n m : ℕ} (sets : Fin m → Finset (Fin n))
    (w x : Fin m → ℝ) : Prop :=
  coverLPFeasible sets x ∧ ∀ y, coverLPFeasible sets y → coverLPCost w x ≤ coverLPCost w y

/-- Exactly the inclusive threshold of Section 1.3; no cap x <= 1 is imposed. -/
noncomputable def coverThreshold {n m : ℕ} (sets : Fin m → Finset (Fin n))
    (x : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => 1 / (coverMaxFrequency sets : ℝ) ≤ x j

/-- The algorithm's input contains costs and incidence only, not an LP solution. -/
structure CoverRoundingInput where
  n : ℕ
  m : ℕ
  sets : Fin m → Finset (Fin n)
  weight : Fin m → ℚ

/-- Dense incidence matrix in set-major order, dimensions and exact rational costs.
All encoders are reused from earlier book-local computational statements. -/
def coverEncodeInput (I : CoverRoundingInput) : List Computability.Γ' :=
  lptEncodeNaturals ([I.n, I.m] ++
    (List.ofFn fun j : Fin I.m =>
      List.ofFn fun i : Fin I.n => if i ∈ I.sets j then 1 else 0).flatten) ++
  maxsatEncodeRationals (List.ofFn I.weight)

end WilliamsonShmoys
