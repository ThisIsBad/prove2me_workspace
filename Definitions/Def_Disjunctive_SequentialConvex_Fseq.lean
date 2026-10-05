import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

namespace Disjunctive.SequentialConvex

/-- The recursive sequential-convexification construction `F_j` (Balas §3.1, p. 42, Theorem 3.1):
`F_0 := F₀`, and for `j = 1, …, |S|` (given an arbitrary ordering `σ` of `S`), `F_j := conv[⋃_{i ∈
Q_{σ(j-1)}} (F_{j-1} ∩ {x : d_i x ≥ d_{i0}})]`. Steps past `|S|` leave the set unchanged. -/
def Fseq {n : ℕ} {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (F0 : Set (Fin n → ℝ)) (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) : ℕ → Set (Fin n → ℝ)
  | 0 => F0
  | k + 1 =>
    if h : k < Fintype.card S then
      convexHull ℝ
        (⋃ i : Qidx (σ ⟨k, h⟩),
          Fseq Qidx F0 d d0 σ k ∩ HalfspaceGE (d (σ ⟨k, h⟩) i) (d0 (σ ⟨k, h⟩) i))
    else
      Fseq Qidx F0 d d0 σ k

end Disjunctive.SequentialConvex
