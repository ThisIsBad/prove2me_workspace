import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.4, p. 97. Let A.1–A.5 and Assumption C̃ hold, with the closed set `B̄ ⊆ B` and
the scalars `m`, `ρ`, `α` of C̃.
(a) `J* ∈ B̄ ∩ F*` and `J*` is the unique fixed point of `T` within `B̄ ∩ F*`; if `J' ∈ B̄ ∩ F*`
and `T(J') ≤ J'` then `J* ≤ J'`, while if `J' ≤ T(J')` then `J' ≤ J*`.
(b) For every `μ ∈ M̃`, `J_μ ∈ B̄ ∩ F̃` and `J_μ` is the unique fixed point of `T_μ` within
`B̄ ∩ F̃`.
(c) `‖T^N(J) − J*‖ → 0` for all `J ∈ B̄ ∩ F*`, and `‖T_μ^N(J) − J_μ‖ → 0` for all `J ∈ B̄ ∩ F̃`,
`μ ∈ M̃`.
(d) A stationary policy `(μ*, μ*, …) ∈ Π̃` is optimal iff `T_{μ*}(J*) = T(J*)`; equivalently,
iff `J_{μ*} ∈ B̄ ∩ F*` and `T_{μ*}(J_{μ*}) = T(J_{μ*})`.
(e) For every `ε > 0` there is a stationary `(μ_ε, μ_ε, …) ∈ Π̃` with `‖J* − J_{μ_ε}‖ ≤ ε`.

The sup-norm statements are written with `SupDistLe`: `‖G − G'‖ ≤ c` means `G`, `G'` are real at
every point and `|G(x) − G'(x)| ≤ c` for all `x`; convergence in (c) is "for every `ε > 0` the
distance is eventually `≤ ε`". -/
theorem prop6_4_contraction_fixed_point {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α) :
    -- (a)
    (MemBbarInter Bbar P.Fstar P.Jstar ∧ P.T P.Jstar = P.Jstar ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' = J' → J' = P.Jstar) ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' ≤ J' → P.Jstar ≤ J') ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → J' ≤ P.T J' → J' ≤ P.Jstar)) ∧
    -- (b)
    (∀ μ : P.Sel, MemBbarInter Bbar P.Ftil (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.Jmu μ ∧
      ∀ J', MemBbarInter Bbar P.Ftil J' → P.Tmu μ.1 J' = J' → J' = P.Jmu μ) ∧
    -- (c)
    (∀ J, MemBbarInter Bbar P.Fstar J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe (P.T^[N] J) P.Jstar ε) ∧
    (∀ μ : P.Sel, ∀ J, MemBbarInter Bbar P.Ftil J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe ((P.Tmu μ.1)^[N] J) (P.Jmu μ) ε) ∧
    -- (d)
    (∀ μ : P.Sel,
      (P.IsOptimal (P.stationary μ) ↔ P.Tmu μ.1 P.Jstar = P.T P.Jstar) ∧
      (P.IsOptimal (P.stationary μ) ↔
        MemBbarInter Bbar P.Fstar (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.T (P.Jmu μ))) ∧
    -- (e)
    (∀ ε : ℝ, 0 < ε → ∃ μ : P.Sel, BertsekasShreve.Contraction.SupDistLe P.Jstar (P.Jmu μ) ε) := by sorry

end BertsekasShreve.Generalized

