import Mathlib

namespace TalagrandConc.QPoints

open scoped ENNReal

/-- For `x ∈ Ω^N` and `q` points `y 0, …, y (q-1) ∈ Ω^N`, the number of coordinates
`i` with `x i ∉ {y 0 i, …, y (q-1) i}`: the coordinates of `x` not captured by the `y j`. -/
noncomputable def uncaptured {Ω : Type*} {N q : ℕ} (y : Fin q → Fin N → Ω)
    (x : Fin N → Ω) : ℕ :=
  Nat.card {i : Fin N // ∀ j : Fin q, x i ≠ y j i}

/-- Talagrand's (3.1.1): `f(A_1, …, A_q, x)`, the infimum of `uncaptured y x` over all
choices `y j ∈ A j`. Computed in `ℕ∞`, so it is `⊤` when some `A j` is empty. -/
noncomputable def qDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω))
    (x : Fin N → Ω) : ℕ∞ :=
  ⨅ (y : Fin q → Fin N → Ω) (_ : ∀ j, y j ∈ A j), (uncaptured y x : ℕ∞)

/-- `a ^ n` for an extended natural exponent: `a ^ ⊤ := ⊤` (the limit of `a ^ n` for
`a > 1`, the only bases used in this chapter). -/
noncomputable def epow (a : ℝ≥0∞) : ℕ∞ → ℝ≥0∞ :=
  ENat.recTopCoe ⊤ (fun m : ℕ => a ^ m)

/-- The section `A(ω) = {x ∈ Ω^N : (x, ω) ∈ A}` of `A ⊆ Ω^{N+1}` (Talagrand (2.1.5));
`(x, ω)` is `Fin.snoc x ω`, the last coordinate being `ω`. -/
def sliceAt {Ω : Type*} {N : ℕ} (A : Set (Fin (N + 1) → Ω)) (ω : Ω) : Set (Fin N → Ω) :=
  {x | (Fin.snoc x ω : Fin (N + 1) → Ω) ∈ A}

/-- The projection `B = {x ∈ Ω^N : ∃ ω, (x, ω) ∈ A}` of `A ⊆ Ω^{N+1}` on `Ω^N`. -/
def projLast {Ω : Type*} {N : ℕ} (A : Set (Fin (N + 1) → Ω)) : Set (Fin N → Ω) :=
  {x | ∃ ω : Ω, (Fin.snoc x ω : Fin (N + 1) → Ω) ∈ A}

end TalagrandConc.QPoints
