import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame

namespace TheoryOfGames.CharFun

namespace ZeroSumGame

variable {n : ℕ} (Γ : ZeroSumGame n)

/-- The aggregate `τ^S` of the choices of the members of a coalition `S ⊆ I` (25.1.3): one
pure strategy for every `k ∈ S`. For `S = ∅` there is exactly one (empty) aggregate. -/
abbrev CoalStrat (S : Finset (Fin n)) : Type := (k : S) → Fin (Γ.β k)

/-- The full strategy profile `(τ₁, …, τₙ)` formed by the aggregates `τ^S` of `S` and
`τ^{-S}` of its complement `-S = Sᶜ` (footnote 2 on p. 239). -/
def joint (S : Finset (Fin n)) (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ) :
    (k : Fin n) → Fin (Γ.β k) :=
  fun k => if h : k ∈ S then τS ⟨k, h⟩ else τC ⟨k, Finset.mem_compl.mpr h⟩

/-- (25:2): the amount `ℋ̄(τ^S, τ^{-S}) = ∑_{k ∈ S} ℋ_k(τ₁, …, τₙ)` the composite player `S`
(player 1') receives in the two-person game of `S` against `-S`. -/
def coalPayoff (S : Finset (Fin n)) (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ) : ℝ :=
  ∑ k ∈ S, Γ.H (Γ.joint S τS τC) k

/-- The bilinear form `K(ξ, η) = ∑_{τ^S, τ^{-S}} ℋ̄(τ^S, τ^{-S}) ξ_{τ^S} η_{τ^{-S}}` (25.1.3,
p. 240). `ξ` is a weight on the aggregates `τ^S` (one joint distribution over all of `S`'s
strategy tuples) and `η` one on the aggregates `τ^{-S}`. -/
def bilin (S : Finset (Fin n)) (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ) : ℝ :=
  ∑ τS, ∑ τC, Γ.coalPayoff S τS τC * ξ τS * η τC

/-- The characteristic function of the game (25.1.3, 25.2.1):
`v(S) = Max_ξ Min_η K(ξ, η)`, where `ξ` ranges over the probability vectors on the aggregates
`τ^S` (mixed strategies of the composite player `S`) and `η` over the probability vectors on
the aggregates `τ^{-S}`. It is defined for every subset `S` of `I`, including `∅` and `I`
(footnote 2 on p. 241). Both simplices are nonempty (every `β k ≥ 1`) and `K` is bounded on
them, so the supremum and infimum below are the book's attained Max and Min. -/
noncomputable def charFun (S : Finset (Fin n)) : ℝ :=
  ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
    Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)

end ZeroSumGame

end TheoryOfGames.CharFun
