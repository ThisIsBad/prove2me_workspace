import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Theorem 7.7 (Balas, *Disjunctive Programming*, Springer 2018, §7.3, p. 95, [112]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`, so that the Sherali-Adams
multiplication applies to them as well), `K_t ⊆ P_{i₁,…,i_t}(K)` for every duplicate-free
sequence `i₁,…,i_t` of `t` indices of `N'` (the book's statement is the case `1,…,t`; `K_t` is
symmetric in the indices of `N'`).
Corrected: the retired version allowed systems without the bound rows, and stated the right-hand
side as `conv(K ∩ {x_S ∈ {0,1}})` instead of the iterated operator `P_{i₁,…,i_t}(K)`. -/
theorem sherali_adams_subset_iterated_split_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (t : ℕ)
    (l : List (Fin n)) (hnd : l.Nodup) (hl : ∀ j ∈ l, j ∈ Nprime) (hlen : l.length = t) :
    KtSet A b Nprime t ⊆ IteratedSplit (Poly A b) l := by sorry

end Disjunctive.HigherDim

