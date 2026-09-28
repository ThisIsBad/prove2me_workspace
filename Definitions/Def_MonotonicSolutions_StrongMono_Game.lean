import Mathlib

namespace MonotonicSolutions.StrongMono

/-- A cooperative game on the player set `N = Fin n` (Young 1985, p. 65): a real-valued
function on coalitions `S ⊆ N` with `v ∅ = 0`. Superadditivity is not required.
The paper's player `k ∈ {1, …, n}` is the Lean index one below `k`. -/
def Game (n : ℕ) : Type := {v : Finset (Fin n) → ℝ // v ∅ = 0}

/-- An allocation procedure (Young 1985, p. 66): a map `φ` assigning to every game `v` on `N`
an allocation `φ v : Fin n → ℝ` that is efficient, `∑_{i ∈ N} (φ v) i = v N`. -/
def IsAllocationProcedure {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, ∑ i, φ v i = v.1 Finset.univ

/-- The marginal contribution `v^i(S)` of player `i` to the coalition `S`, Eq. (3) of
Young (1985, p. 67): `v S - v (S - i)` if `i ∈ S`, and `v (S + i) - v S` if `i ∉ S`.
It is defined for every coalition `S`. -/
def marginal {n : ℕ} (v : Finset (Fin n) → ℝ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  if i ∈ S then v S - v (S.erase i) else v (insert i S) - v S

end MonotonicSolutions.StrongMono
