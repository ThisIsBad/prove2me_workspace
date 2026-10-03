import Mathlib

namespace Disjunctive.Polarity

/-- The polyhedron `{x : A x ≥ b}` (Balas §2.1, restated locally here since a draft mission
cannot import another draft mission's definitions). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- The disjunctive set `F := ⋃_{h ∈ Q} P_h` (restated locally, as in `02a-convex-hull`). -/
def DisjunctiveSet {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) : Set (Fin n → ℝ) :=
  ⋃ h : Q, Poly (A h) (b h)

/-- `Q* := {h ∈ Q : P_h ≠ ∅}` (restated locally). -/
def FeasibleIndices {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) : Set Q :=
  {h | (Poly (A h) (b h)).Nonempty}

/-- The (ordinary) polar `S⁰ := {x ∈ ℝⁿ : xy ≤ 1, ∀ y ∈ S}` of a set `S` (Balas §2.4, p. 31). -/
def Polar {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ y ∈ S, dotProduct x y ≤ 1}

/-- The reverse polar `S# := {x ∈ ℝⁿ : xy ≥ 1, y ∈ S}` of a set `S` (Balas §2.4, p. 31, [6, 10]).
-/
def ReversePolar {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ y ∈ S, 1 ≤ dotProduct x y}

/-- The (finite, nonnegative) conic hull of a set `S`: the smallest cone containing `S` (Balas
§2.4, p. 32, `cl cone S` in Theorem 2.14 is the closure of this set). -/
def ConeHull {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ (k : ℕ) (c : Fin k → ℝ) (y : Fin k → (Fin n → ℝ)),
    (∀ i, 0 ≤ c i ∧ y i ∈ S) ∧ x = ∑ i, c i • y i}

/-- The scaled polar `F_(α₀) := {y ∈ ℝⁿ : xy ≥ α₀, ∀ x ∈ F}` of a set `F` with scaling factor
`α₀` (Balas §2.4, p. 35): the reverse polar when `α₀ = 1`, the negative ordinary polar when
`α₀ = -1`, and the negative polar cone when `α₀ = 0`. -/
def ScaledPolar {n : ℕ} (F : Set (Fin n → ℝ)) (α0 : ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ F, α0 ≤ dotProduct x y}

/-- The cone `W₀ := {(α, α₀) : ∃ (u_h)_{h ∈ Q*}, α - u_h A_h = 0, α₀ - u_h b_h ≤ 0, u_h ≥ 0}`
(Balas §2.4, p. 35), the projection onto `(α, α₀)` of the projection cone `W` used in Theorem
2.1's second proof: the same `α, α₀` must work simultaneously for every `h ∈ Q*` (each with its
own multiplier `u_h`), exactly as in Theorem 1.2's valid-inequality characterization. -/
def W0 {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ) (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ)
    (b : (h : Q) → Fin (m h) → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p | ∃ u : (h : Q) → Fin (m h) → ℝ, ∀ h ∈ FeasibleIndices m A b,
        Matrix.vecMul (u h) (A h) = p.1 ∧ p.2 ≤ dotProduct (u h) (b h) ∧ 0 ≤ u h}

end Disjunctive.Polarity
