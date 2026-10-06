import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet

namespace SteinitzExchange.LocalSupermod

/-- A set function `f : 2^V → β` is submodular if `f(X) + f(Y) ≥ f(X ∪ Y) + f(X ∩ Y)` for all
`X, Y ⊆ V` (Murota 1996, p. 277, Eq. (2.1)). Used with `β = ℤ` (Theorem 2.1) and `β = ℝ`. -/
def IsSubmodular {V : Type*} [DecidableEq V] {β : Type*} [Add β] [LE β]
    (f : Finset V → β) : Prop :=
  ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

/-- A set function `g : 2^V → β` is supermodular if `g(X) + g(Y) ≤ g(X ∪ Y) + g(X ∩ Y)` for all
`X, Y ⊆ V` (Murota 1996, p. 277, Eq. (2.2)). Used with `β = ℤ` (Theorem 2.1) and `β = ℝ`
(condition (C1)). -/
def IsSupermodular {V : Type*} [DecidableEq V] {β : Type*} [Add β] [LE β]
    (g : Finset V → β) : Prop :=
  ∀ X Y : Finset V, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)

/-- `h : ℝ^V → ℝ` is positively homogeneous: `h(λp) = λ h(p)` for every `λ > 0`
(Murota 1996, p. 290). -/
def IsPosHomogeneous {V : Type*} (h : (V → ℝ) → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ p : V → ℝ, h (c • p) = c * h p

/-- Condition (C1) [supermodularity] (Murota 1996, p. 290) for `h : ℝ^V → ℝ`:
the set function `g(X) := h(χ_X)` is supermodular. -/
def SatisfiesC1 {V : Type*} [DecidableEq V] (h : (V → ℝ) → ℝ) : Prop :=
  IsSupermodular (fun X : Finset V => h (charVec X))

/-- Condition (C2) [greediness] (Murota 1996, p. 290) for `h : ℝ^V → ℝ`:
`h(p) = ∑_{j=1}^n (p_j − p_{j+1}) h(χ_{V_j})` whenever the elements of `V` are indexed as
`v₁, …, v_n` (`n = |V|`) with `p(v₁) ≥ ⋯ ≥ p(v_n)`, where `p_j = p(v_j)`,
`V_j = {v₁, …, v_j}` and `p_{n+1} = 0`. An indexing is a bijection `σ : Fin n ≃ V`
(`σ j = v_{j+1}`, 0-based); the identity is required for **every** indexing with `p ∘ σ`
antitone. -/
def SatisfiesC2 {V : Type*} [Fintype V] [DecidableEq V] (h : (V → ℝ) → ℝ) : Prop :=
  ∀ (p : V → ℝ) (σ : Fin (Fintype.card V) ≃ V), Antitone (p ∘ σ) →
    h p = ∑ j : Fin (Fintype.card V),
      (p (σ j) - (if hj : (j : ℕ) + 1 < Fintype.card V then p (σ ⟨(j : ℕ) + 1, hj⟩) else 0)) *
        h (charVec (Finset.univ.filter (fun v => σ.symm v ≤ j)))

/-- A positively homogeneous `h : ℝ^V → ℝ` is "matroidal" if it satisfies (C1) and (C2)
(Murota 1996, p. 291). Positive homogeneity is part of the definition. -/
def IsMatroidal {V : Type*} [Fintype V] [DecidableEq V] (h : (V → ℝ) → ℝ) : Prop :=
  IsPosHomogeneous h ∧ SatisfiesC1 h ∧ SatisfiesC2 h

/-- `ψ°(p) = min{⟨p, x⟩ | x ∈ B}` for a finite nonempty `B ⊆ ℤ^V` (Murota 1996, p. 289,
Eq. (5.1)). For nonempty `B` the infimum over the finite index set is attained, so it is the
minimum; for empty `B` the value is the junk value `0`, and every statement assumes `B`
nonempty. -/
noncomputable def supportMin {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (p : V → ℝ) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), pairing p (toReal (x : V → ℤ))

end SteinitzExchange.LocalSupermod
