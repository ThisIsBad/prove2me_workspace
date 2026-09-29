import Mathlib

namespace SteinitzExchange.Duality

/-- The characteristic vector `χ_u ∈ ℤ^V` of `u ∈ V`: `χ_u(v) = 1` if `v = u`, else `0`
(Murota 1996, p. 276, §2.1). -/
def chi {V : Type*} [DecidableEq V] (u : V) : V → ℤ :=
  Pi.single u 1

/-- The embedding `ℤ^V → ℝ^V`, `x ↦ (x(v) : ℝ)_{v ∈ V}`. -/
def toReal {V : Type*} (x : V → ℤ) : V → ℝ :=
  fun v => (x v : ℝ)

/-- The pairing `⟨p, b⟩ = ∑_{v ∈ V} p(v) b(v)` on `ℝ^V` (Murota 1996, p. 276, §2.1). -/
def pairing {V : Type*} [Fintype V] (p b : V → ℝ) : ℝ :=
  ∑ v, p v * b v

/-- `x(X) = ∑_{v ∈ X} x(v)` for an integer vector `x` and `X ⊆ V` (Murota 1996, p. 276, §2.1). -/
def sumOn {V : Type*} (x : V → ℤ) (X : Finset V) : ℤ :=
  ∑ v ∈ X, x v

/-- `B̄`: the convex hull in `ℝ^V` of a finite set `B ⊆ ℤ^V` (Murota 1996, p. 285, Eq. (4.4)). -/
def hull {V : Type*} (B : Finset (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (toReal '' (B : Set (V → ℤ)))

/-- A finite integral base set (Murota 1996, p. 277, (B1)): a finite nonempty `B ⊆ ℤ^V` such that
for `x, y ∈ B` and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`. -/
def IsIntegralBaseSet {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) : Prop :=
  B.Nonempty ∧
    ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
      ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B

end SteinitzExchange.Duality
