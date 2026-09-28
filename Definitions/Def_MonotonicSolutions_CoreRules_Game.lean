import Mathlib

namespace MonotonicSolutions.CoreRules

/-- A cooperative game on the player set `N = Fin n` (Young 1985, p. 65): a real-valued
function on coalitions `S ⊆ N` with `v ∅ = 0`. Superadditivity is not required.
The paper's player `k ∈ {1, …, n}` is the Lean index one below `k`. -/
def Game (n : ℕ) : Type := {v : Finset (Fin n) → ℝ // v ∅ = 0}

/-- An allocation procedure (Young 1985, p. 66): a map `φ` assigning to every game `v` on `N`
an allocation `φ v : Fin n → ℝ` that is efficient, `∑_{i ∈ N} (φ v) i = v N`. -/
def IsAllocationProcedure {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, ∑ i, φ v i = v.1 Finset.univ

end MonotonicSolutions.CoreRules
