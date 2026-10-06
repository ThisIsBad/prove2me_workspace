import Mathlib

namespace SecretaryWD.DiscUpper

/-- The average of `f` over the uniformly random arrival order: `(1/n!) · ∑_π f π`, where
`π : Equiv.Perm (Fin n)` is read as *time ↦ element*. -/
noncomputable def uniformAvg {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), f π

/-- The tie-break key of element `e` under values `v`: compare `(v e, e)` lexicographically,
larger value first and, among equal values, the **smaller index** first (hence `OrderDual`). -/
def tieKey {k : ℕ} (v : Fin k → ℝ) (e : Fin k) : Lex (ℝ × (Fin k)ᵒᵈ) :=
  toLex (v e, OrderDual.toDual e)

/-- The classical secretary rule (§2, p. 4) on `m` arrivals whose keys, in arrival order, are
`x 0, …, x (m-1)` in a linear order. It skips the first `⌊m / e⌋` arrivals, then selects the
first arrival `t` (index `t ≥ ⌊m/e⌋`) whose key is strictly larger than the key of every earlier
arrival, the skipped ones included. It returns the index of the selected arrival, or `none`. -/
noncomputable def classicalSecretary {α : Type*} [LinearOrder α] (m : ℕ) (x : Fin m → α) :
    Option (Fin m) :=
  (List.finRange m).find? fun t =>
    decide (Nat.floor ((m : ℝ) / Real.exp 1) ≤ t.val ∧ ∀ s : Fin m, s < t → x s < x t)

end SecretaryWD.DiscUpper
