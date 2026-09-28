import Mathlib

namespace JohnsonApprox.SubsetSum

/-- An input `⟨T, s, b⟩` of SUBSET-SUM (Johnson 1974, p. 259): a finite set `T`, a size map
`s` that is a positive rational on every element of `T`, and a positive rational bound `b`. -/
structure Input (α : Type) where
  /-- The finite ground set `T`. -/
  T : Finset α
  /-- The size map `s : T → Q+` (only its values on `T` matter). -/
  s : α → ℚ
  /-- The bound `b`. -/
  b : ℚ
  s_pos : ∀ x ∈ T, 0 < s x
  b_pos : 0 < b

variable {α : Type}

/-- The measure `m_SS(T') = Σ_{x ∈ T'} s(x)`. -/
def measure (u : Input α) (T' : Finset α) : ℚ := ∑ x ∈ T', u.s x

/-- `T'` is an approximate solution: `T' ⊆ T` and `Σ_{x ∈ T'} s(x) ≤ b`. -/
def IsFeasible (u : Input α) (T' : Finset α) : Prop :=
  T' ⊆ u.T ∧ measure u T' ≤ u.b

/-- The finite set `SOL_SS(⟨T, s, b⟩)` of approximate solutions. -/
def feasibleSet (u : Input α) : Finset (Finset α) :=
  u.T.powerset.filter (fun T' => measure u T' ≤ u.b)

/-- The empty set is always an approximate solution, so `SOL_SS` is nonempty. -/
theorem empty_mem_feasibleSet (u : Input α) : (∅ : Finset α) ∈ feasibleSet u := by
  unfold feasibleSet
  rw [Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset _, ?_⟩
  rw [measure, Finset.sum_empty]
  exact u.b_pos.le

/-- The optimal measure `⟨T, s, b⟩* = MAX{m(T') : T' ⊆ T and m(T') ≤ b}`, a maximum over the
finite nonempty set of approximate solutions. -/
def opt (u : Input α) : ℚ :=
  (feasibleSet u).sup' ⟨∅, empty_mem_feasibleSet u⟩ (measure u)

end JohnsonApprox.SubsetSum
