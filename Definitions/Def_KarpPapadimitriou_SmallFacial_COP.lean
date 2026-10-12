import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace KarpPapadimitriou.SmallFacial

/-- The data used by Lemma 1: feasible nonnegative integer vectors indexed by binary inputs.
The complexity conditions of Definition 1 are not needed for this lemma. -/
structure COP where
  L : Set (List Bool)
  n : List Bool → ℕ
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  S_nonneg : ∀ z ∈ L, ∀ x ∈ S z, ∀ i, 0 ≤ x i

/-- The paper's `CH(S(z))`, with its `R` interpreted as the rationals. -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ {x | ∃ y ∈ C.S z, x = fun i => (y i : ℚ)}

/-- A collection of input-indexed integral inequalities describes every rational hull. -/
def IsFacialDescription (C : COP)
    (F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)) : Prop :=
  (∀ t ∈ F, t.1 ∈ C.L) ∧
  ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
    x ∈ hull C z ↔
      ∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
        ⟨z, (f, g)⟩ ∈ F → (∑ i, (f i : ℚ) * x i) ≤ (g : ℚ)

/-- One polynomial bound works for all inputs and all inequalities. -/
def IsSmall (C : COP)
    (F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)) : Prop :=
  ∃ k : ℕ, ∀ t ∈ F,
    (∀ i, Int.natAbs (t.2.1 i) ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k)) ∧
    Int.natAbs t.2.2 ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k)

/-- Every feasible vector has zero-one entries. -/
def IsZeroOne (C : COP) : Prop :=
  ∀ z ∈ C.L, ∀ x ∈ C.S z, ∀ i, x i = 0 ∨ x i = 1

/-- A vertex, equivalently an extreme point, of a rational convex set. -/
def IsVertex {n : ℕ} (Q : Set (Fin n → ℚ)) (v : Fin n → ℚ) : Prop :=
  v ∈ Q ∧ ∀ a ∈ Q, ∀ b ∈ Q, ∀ r : ℚ,
    0 < r → r < 1 → v = r • a + (1 - r) • b → a = v ∧ b = v

/-- A nonzero recession direction based at some point of a rational set. -/
def HasRay {n : ℕ} (Q : Set (Fin n → ℚ)) : Prop :=
  ∃ (v : Fin n → ℚ) (d : Fin n → ℚ),
    v ∈ Q ∧ d ≠ 0 ∧ ∀ r : ℚ, 0 ≤ r → v + r • d ∈ Q

/-- The binary length used on p. 6 for one integer entry. -/
def entrySize (a : ℤ) : ℕ := Nat.clog 2 (1 + a.natAbs)

/-- The paper's `s`, summed over every entry of the integer matrix and right-hand side. -/
def inputSize {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : ℕ :=
  (∑ i, ∑ j, entrySize (A i j)) + ∑ i, entrySize (b i)

/-- Inputs encode systems of integral inequalities, and feasible vectors are exactly their
nonnegative integer solutions. The length bound makes the binary encoding explicit. -/
def IsIPType (C : COP) : Prop :=
  ∃ (m : List Bool → ℕ)
    (A : ∀ z, Matrix (Fin (m z)) (Fin (C.n z)) ℤ)
    (b : ∀ z, Fin (m z) → ℤ),
    ∀ z ∈ C.L,
      inputSize (A z) (b z) ≤ z.length ∧
      C.S z = {x | (∀ j, 0 ≤ x j) ∧
        (fun j => (x j : ℚ)) ∈
          CookSensitivity.ChvatalRank.polyhedron (A z) (fun i => (b z i : ℚ))}

end KarpPapadimitriou.SmallFacial
