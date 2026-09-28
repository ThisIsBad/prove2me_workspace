import Mathlib

namespace JohnsonApprox.SetCover

/-!
SET COVERING I (Johnson 1974, Section 5, pp. 264–265).

An input is a finite family `{S_1, …, S_p}` of finite sets, given as an indexed family
`S : ι → Finset α` over a finite index type `ι` (the paper's `1, …, p`). The indices are what
algorithm C1 chooses from ("Choose j ≤ N"). Two indices may carry the same set.
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- The family `F = {S_i : i ∈ ι}` as a finite set of finite sets. -/
def family (S : ι → Finset α) : Finset (Finset α) := Finset.univ.image S

/-- The set to be covered, `T = ⋃_{S ∈ F} S`. -/
def ground (S : ι → Finset α) : Finset α := Finset.univ.biUnion S

/-- The feasible solutions `SOL_SC(F) = {F' ⊆ F : ⋃_{S ∈ F'} S = ⋃_{S ∈ F} S}` (the subcovers). -/
def subcovers (S : ι → Finset α) : Finset (Finset (Finset α)) :=
  (family S).powerset.filter (fun F' => F'.biUnion id = ground S)

/-- `F` itself is a subcover, so `SOL_SC(F)` is nonempty. -/
theorem family_mem_subcovers (S : ι → Finset α) : family S ∈ subcovers S := by
  unfold subcovers family ground
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset_self _, by rw [Finset.image_biUnion]; rfl⟩

/-- The optimal measure `F* = MIN{|F'| : F' ∈ SOL_SC(F)}` (with `m_SC(F') = |F'|`), a minimum
over a finite nonempty set. -/
def opt (S : ι → Finset α) : ℕ :=
  (subcovers S).inf' ⟨family S, family_mem_subcovers S⟩ Finset.card

/-- `F` is an input of `SC(k)`: no set of the family has more than `k` elements. -/
def InSC (k : ℕ) (S : ι → Finset α) : Prop := ∀ i, (S i).card ≤ k

end JohnsonApprox.SetCover
