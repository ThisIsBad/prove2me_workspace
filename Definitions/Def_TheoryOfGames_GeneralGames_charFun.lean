import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame

namespace TheoryOfGames.GeneralGames

namespace GeneralGame

variable {n : ℕ} (Γ : GeneralGame n)

/-- The payoffs of the zero-sum extension `Γ̄` (56.2.2, (56:2)): the players of `Γ̄` are
`Ī = Fin (n + 1)`, the real player `k` is `Fin.castSucc k` and the fictitious player `n + 1` is
`Fin.last n`. The real players get `ℋ_k(τ₁, …, τₙ)`; the fictitious player gets
`ℋ_{n+1}(τ₁, …, τₙ) ≡ -∑_{k=1}^n ℋ_k(τ₁, …, τₙ)`. The fictitious player has no variable of
his own (equivalently, a single strategy, footnote 2 on p. 506). -/
def extH (τ : (k : Fin n) → Fin (Γ.β k)) : Fin (n + 1) → ℝ :=
  Fin.lastCases (motive := fun _ => ℝ) (-(∑ k, Γ.H τ k)) (fun i => Γ.H τ i)

/-- The real members `S ∩ I` of a set `S ⊆ Ī = Fin (n + 1)`, as a subset of `I = Fin n`. -/
def realPart (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ S)

/-- The aggregate `τ^S` of the choices of the (real) members of a set `R ⊆ I` (25.1.3): one
pure strategy for every `k ∈ R`. For `R = ∅` there is exactly one (empty) aggregate. -/
abbrev CoalStrat (R : Finset (Fin n)) : Type := (k : R) → Fin (Γ.β k)

/-- The full profile `(τ₁, …, τₙ)` formed by the aggregates of `R` and of its complement `I - R`. -/
def joint (R : Finset (Fin n)) (τS : Γ.CoalStrat R) (τC : Γ.CoalStrat Rᶜ) :
    (k : Fin n) → Fin (Γ.β k) :=
  fun k => if h : k ∈ R then τS ⟨k, h⟩ else τC ⟨k, Finset.mem_compl.mpr h⟩

/-- (25:2) applied to `Γ̄`: the amount `∑_{k ∈ S} ℋ̄_k` that the composite player `S ⊆ Ī`
receives in the two-person game of `S` against `Ī - S`, when the real members of `S` play the
aggregate `τS` and the real members of `Ī - S` play `τC`. -/
def coalPayoff (S : Finset (Fin (n + 1))) (τS : Γ.CoalStrat (realPart S))
    (τC : Γ.CoalStrat (realPart S)ᶜ) : ℝ :=
  ∑ k ∈ S, Γ.extH (Γ.joint (realPart S) τS τC) k

/-- The bilinear form `K(ξ, η) = ∑_{τ^S, τ^{Ī-S}} ℋ̄(τ^S, τ^{Ī-S}) ξ_{τ^S} η_{τ^{Ī-S}}` (25.1.3
applied to `Γ̄`). `ξ` is one joint weight on all the strategy tuples of the members of `S`. -/
def bilin (S : Finset (Fin (n + 1))) (ξ : Γ.CoalStrat (realPart S) → ℝ)
    (η : Γ.CoalStrat (realPart S)ᶜ → ℝ) : ℝ :=
  ∑ τS, ∑ τC, Γ.coalPayoff S τS τC * ξ τS * η τC

/-- The *extended characteristic function* of `Γ` (57.1, 57.2.1): the characteristic function
(25.1.3) of the zero-sum extension `Γ̄`, defined for every `S ⊆ Ī = (1, …, n, n + 1)`:
`v(S) = Max_ξ Min_η K(ξ, η)`, with `ξ` ranging over the probability vectors on the aggregates of
`S` and `η` over those on the aggregates of `Ī - S`. The fictitious player's single strategy is
omitted from the aggregates (it does not change them). Both simplices are nonempty (every
`β k ≥ 1`) and `K` is bounded on them, so `⨆`/`⨅` are the book's attained Max/Min. -/
noncomputable def extCharFun (S : Finset (Fin (n + 1))) : ℝ :=
  ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (realPart S)),
    ⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (realPart S) → ℝ) (η : Γ.CoalStrat (realPart S)ᶜ → ℝ)

/-- The *restricted characteristic function* of `Γ` (57.1, 57.2.1): the extended one on the
sets `S ⊆ I = (1, …, n)` only (`S` viewed inside `Ī` via `Fin.castSucc`). For a zero-sum `Γ`
it is the characteristic function of 25.1.3 (57.1, p. 528). -/
noncomputable def restrictedCharFun (S : Finset (Fin n)) : ℝ :=
  Γ.extCharFun (S.map Fin.castSuccEmb)

end GeneralGame

end TheoryOfGames.GeneralGames
