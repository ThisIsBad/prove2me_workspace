import Mathlib

namespace JohnsonApprox.ExactCover

/-- An input of SET COVERING II (EC): a finite family `{S_1, …, S_p}` of finite sets, indexed by
`Fin p` (0-based). Repeated sets are allowed. -/
structure Input (α : Type) where
  p : ℕ
  S : Fin p → Finset α

variable {α : Type} [DecidableEq α]

/-- The covered set `T = ⋃_{S ∈ F} S`. -/
def Input.ground (F : Input α) : Finset α := Finset.univ.biUnion F.S

/-- `SOL_EC(F)`: the index set `M` describes a subcover, `⋃_{i ∈ M} S_i = ⋃_{S ∈ F} S`. -/
def Input.IsSubcover (F : Input α) (M : Finset (Fin F.p)) : Prop := M.biUnion F.S = F.ground

instance (F : Input α) (M : Finset (Fin F.p)) : Decidable (F.IsSubcover M) := by
  unfold Input.IsSubcover; infer_instance

/-- `m_EC(F′) = Σ_{S ∈ F′} |S|`. -/
def Input.measure (F : Input α) (M : Finset (Fin F.p)) : ℕ := ∑ i ∈ M, (F.S i).card

/-- The finite set of all subcovers (as index sets). -/
def Input.subcovers (F : Input α) : Finset (Finset (Fin F.p)) :=
  Finset.univ.filter F.IsSubcover

theorem Input.univ_mem_subcovers (F : Input α) : Finset.univ ∈ F.subcovers := by
  simp [Input.subcovers, Input.IsSubcover, Input.ground]

theorem Input.subcovers_nonempty (F : Input α) : F.subcovers.Nonempty :=
  ⟨_, F.univ_mem_subcovers⟩

/-- The optimum `F* = MIN {m_EC(F′) : F′ ∈ SOL_EC(F)}`, a minimum over a finite nonempty set. -/
def Input.opt (F : Input α) : ℕ := F.subcovers.inf' F.subcovers_nonempty F.measure

/-- `EC(k)`: no set of the family contains more than `k` points. -/
def InEC (k : ℕ) (F : Input α) : Prop := ∀ i, (F.S i).card ≤ k

end JohnsonApprox.ExactCover
