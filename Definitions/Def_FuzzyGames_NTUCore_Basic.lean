import Mathlib

namespace FuzzyGames.NTUCore

open Set Finset Pointwise

variable {n : ℕ}

/-- The cube `[0,1]^n` of fuzzy coalitions (§1, p. 2), in the coordinatewise order. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

/-- The nonnegative orthant `ℝ^n_+`, the domain of a fuzzy game after its extension by
positive homogeneity (§3, p. 3). -/
def orthant (n : ℕ) : Set (Fin n → ℝ) := Set.Ici 0

/-- `τ^A`, the characteristic vector of the coalition `A ⊆ N` (§1, p. 2).
`τ^N` is `coal Finset.univ`, the vector `(1, …, 1)`. -/
def coal (A : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ A then 1 else 0

/-- The coordinatewise product `τ · c`, `(τ · c)_i = τ_i c_i` (§3 (1)). -/
def tmul (τ c : Fin n → ℝ) : Fin n → ℝ := fun i => τ i * c i

/-- `ℝ^τ = τ · ℝ^n` (§3 (2)): for `τ ≥ 0`, the vectors vanishing off the support
`A_τ = {i | τ_i > 0}`. -/
def Rtau (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | ∀ i, τ i = 0 → c i = 0}

/-- `ℝ^τ_+ = τ · ℝ^n_+` (§3 (2)): nonnegative vectors vanishing off `A_τ`. -/
def RtauNonneg (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | c ∈ Rtau τ ∧ ∀ i, 0 ≤ c i}

/-- `ℝ̊^τ_+ = τ · ℝ̊^n_+` (§3 (2)): vectors strictly positive on `A_τ` and zero off it. -/
def RtauPos (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {c | c ∈ Rtau τ ∧ ∀ i, 0 < τ i → 0 < c i}

/-- The support function `λ ↦ sup_{c ∈ W} Σ_i λ_i c_i` of a set `W ⊆ ℝ^n`, valued in `EReal`
(it is `+∞` when the sup is unbounded and `⊥ = -∞` when `W = ∅`). -/
noncomputable def supportFn (W : Set (Fin n → ℝ)) (l : Fin n → ℝ) : EReal :=
  ⨆ c ∈ W, ((∑ i, l i * c i : ℝ) : EReal)

/-- `M^τ = {λ ∈ ℝ^τ_+ | Σ_{i ∈ A_τ} λ^i = 1}` (§3 (6)). `M^n` is `simplexOn (coal univ)`. -/
def simplexOn (τ : Fin n → ℝ) : Set (Fin n → ℝ) := {l | l ∈ RtauNonneg τ ∧ ∑ i, l i = 1}

/-- `M̊^τ = M^τ ∩ ℝ̊^τ_+` (§3 (6)). `M̊^n` is `simplexOnPos (coal univ)`. -/
def simplexOnPos (τ : Fin n → ℝ) : Set (Fin n → ℝ) := simplexOn τ ∩ RtauPos τ

/-! ### Fuzzy games without side payments (§3) -/

/-- A **fuzzy game without side payments** (§3 (3)), encoded on the orthant `τ ≥ 0` to which the
paper extends it by positive homogeneity: for every `τ ≥ 0`, `V(τ)` is a nonempty, closed, convex
subset of `ℝ^τ`, comprehensive (`V(τ) = V(τ) − ℝ^τ_+`) and bounded above
(`V(τ) ⊆ C − ℝ^τ_+` for some `C ∈ ℝ^τ`); and `V(tτ) = t V(τ)` for all `t > 0`. -/
structure IsNTUFuzzyGame (V : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop where
  subset_Rtau : ∀ τ ∈ orthant n, V τ ⊆ Rtau τ
  nonempty : ∀ τ ∈ orthant n, (V τ).Nonempty
  isClosed : ∀ τ ∈ orthant n, IsClosed (V τ)
  convex : ∀ τ ∈ orthant n, Convex ℝ (V τ)
  comprehensive : ∀ τ ∈ orthant n, V τ - RtauNonneg τ = V τ
  bddAbove : ∀ τ ∈ orthant n, ∃ C ∈ Rtau τ, V τ ⊆ {C} - RtauNonneg τ
  homogeneous : ∀ t : ℝ, 0 < t → ∀ τ ∈ orthant n, V (t • τ) = t • V τ

/-- Superadditivity (§3 (9) = §5 (1)): `V(τ) + V(σ) ⊆ V(τ + σ)` for all `τ, σ ∈ ℝ^n_+`. -/
def Superadditive (V : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∀ τ ∈ orthant n, ∀ σ ∈ orthant n, V τ + V σ ⊆ V (τ + σ)

/-- The **core of a fuzzy game without side payments** (§3 (4)), for any set-valued map `W`:
`c ∈ W(τ^N)` and no fuzzy coalition `τ ≠ 0` improves upon `c`, i.e.
`τ · c ∉ W(τ) − ℝ̊^τ_+`. -/
def fuzzyCore (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧
    ∀ τ ∈ cube n, τ ≠ 0 → tmul τ c ∉ W τ - RtauPos τ}

/-- The complaint `inf_{λ ∈ M^τ} [v(τ, λ) − Σ_i λ^i τ_i c_i]` of the fuzzy coalition `τ` against
`c` (§3, p. 4), where `v(τ, λ)` is the support function of `W(τ)` (§3 (5)). -/
noncomputable def complaint (W : (Fin n → ℝ) → Set (Fin n → ℝ)) (τ c : Fin n → ℝ) : EReal :=
  ⨅ l ∈ simplexOn τ, (supportFn (W τ) l - ((∑ i, l i * τ i * c i : ℝ) : EReal))

/-- The maximum complaint function `α` (§3 (7)): the supremum of the complaints over the
fuzzy coalitions `τ ∈ [0,1]^n` with `τ ≠ 0`. -/
noncomputable def maxComplaint (W : (Fin n → ℝ) → Set (Fin n → ℝ)) (c : Fin n → ℝ) : EReal :=
  ⨆ τ ∈ {τ : Fin n → ℝ | τ ∈ cube n ∧ τ ≠ 0}, complaint W τ c

/-- Weak canonical cooperative equilibria of a fuzzy game (§3 (8)): `c ∈ W(τ^N)` and some
`λ̄ ∈ M^n` satisfies `v(τ, λ̄) ≤ Σ_i λ̄^i τ_i c_i` for every `τ ∈ [0,1]^n`. -/
def weakCCE (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧ ∃ l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))),
    ∀ τ ∈ cube n, supportFn (W τ) l ≤ ((∑ i, l i * τ i * c i : ℝ) : EReal)}

/-- Strong canonical cooperative equilibria of a fuzzy game (§3, p. 5): as `weakCCE`, with
`λ̄ ∈ M̊^n = M^n ∩ ℝ̊^n_+`. -/
def strongCCE (W : (Fin n → ℝ) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ W (coal Finset.univ) ∧ ∃ l ∈ simplexOnPos (coal (Finset.univ : Finset (Fin n))),
    ∀ τ ∈ cube n, supportFn (W τ) l ≤ ((∑ i, l i * τ i * c i : ℝ) : EReal)}

/-! ### Usual games without side payments on a family of coalitions (§6 (3)–(4), §7) -/

/-- The family `𝒞` of admissible coalitions (§1): it contains `N` and every singleton `{i}`.
The empty coalition is excluded (the paper only ever uses `A ≠ ∅`). -/
structure CoalFamily (n : ℕ) where
  C : Finset (Finset (Fin n))
  univ_mem : (Finset.univ : Finset (Fin n)) ∈ C
  singleton_mem : ∀ i, ({i} : Finset (Fin n)) ∈ C
  empty_not_mem : (∅ : Finset (Fin n)) ∉ C

/-- The balances `𝒞(τ)` of `τ` (§6 (3)–(4)): nonnegative weights `m(A)`, vanishing off `𝒞`, with
`τ_i = Σ_{A ∈ 𝒞, A ∋ i} m(A)` for every player `i`. -/
def balances (𝒞 : CoalFamily n) (τ : Fin n → ℝ) : Set (Finset (Fin n) → ℝ) :=
  {m | (∀ A, 0 ≤ m A) ∧ (∀ A, A ∉ 𝒞.C → m A = 0) ∧
    ∀ i, ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A = τ i}

/-- A **game without side payments** on `𝒞` (§7 (1)): for every `A ∈ 𝒞`, `V(A)` is a nonempty,
closed, convex subset of `ℝ^A = ℝ^{τ^A}`, comprehensive (`V(A) = V(A) − ℝ^A_+`) and bounded above
(`V(A) ⊆ C − ℝ^A_+` for some `C ∈ ℝ^A`). -/
structure IsNTUGame (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Prop where
  subset_Rtau : ∀ A ∈ 𝒞.C, V A ⊆ Rtau (coal A)
  nonempty : ∀ A ∈ 𝒞.C, (V A).Nonempty
  isClosed : ∀ A ∈ 𝒞.C, IsClosed (V A)
  convex : ∀ A ∈ 𝒞.C, Convex ℝ (V A)
  comprehensive : ∀ A ∈ 𝒞.C, V A - RtauNonneg (coal A) = V A
  bddAbove : ∀ A ∈ 𝒞.C, ∃ C ∈ Rtau (coal A), V A ⊆ {C} - RtauNonneg (coal A)

/-- The core of a game without side payments (§7 (2)): `c ∈ V(N)` and
`τ^A · c ∉ V(A) − ℝ̊^A_+` for every `A ∈ 𝒞`. -/
def ntuCore (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∀ A ∈ 𝒞.C, tmul (coal A) c ∉ V A - RtauPos (coal A)}

/-- The support function `v(A, λ) = sup_{c ∈ V(A)} Σ_{i ∈ A} λ^i c_i` of `V(A)` (§7 (4)),
valued in `EReal`. -/
noncomputable def coalSupport (V : Finset (Fin n) → Set (Fin n → ℝ)) (A : Finset (Fin n))
    (l : Fin n → ℝ) : EReal :=
  ⨆ c ∈ V A, ((∑ i ∈ A, l i * c i : ℝ) : EReal)

/-- Weak canonical cooperative equilibria of a game without side payments (§7 (3)):
`c ∈ V(N)` and some `λ̄ ∈ M^n` satisfies `v(A, λ̄) ≤ Σ_{i ∈ A} λ̄^i c_i` for every `A ∈ 𝒞`. -/
def ntuWeakCCE (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∃ l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))),
    ∀ A ∈ 𝒞.C, coalSupport V A l ≤ ((∑ i ∈ A, l i * c i : ℝ) : EReal)}

/-- Strong canonical cooperative equilibria of a game without side payments (§7 (3)): as
`ntuWeakCCE`, with `λ̄ ∈ M̊^n`. -/
def ntuStrongCCE (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {c | c ∈ V Finset.univ ∧ ∃ l ∈ simplexOnPos (coal (Finset.univ : Finset (Fin n))),
    ∀ A ∈ 𝒞.C, coalSupport V A l ≤ ((∑ i ∈ A, l i * c i : ℝ) : EReal)}

/-- The fuzzy extension `πV(τ) = ⋃_{m ∈ 𝒞(τ)} Σ_{A ∈ 𝒞} m(A) V(A)` (§7 (5)), with Minkowski
sums and scalings of sets. -/
def piV (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) (τ : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ m ∈ balances 𝒞 τ, ∑ A ∈ 𝒞.C, m A • V A

/-- `πv(τ, λ) = sup_{m ∈ 𝒞(τ)} Σ_{A ∈ 𝒞} m(A) v(A, λ)` (§7 (10)–(11)), valued in `EReal`. -/
noncomputable def piv (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ l : Fin n → ℝ) : EReal :=
  ⨆ m ∈ balances 𝒞 τ, ∑ A ∈ 𝒞.C, ((m A : ℝ) : EReal) * coalSupport V A l

/-- A game without side payments is **balanced** (§7 (8)) if `V(N) = πV(τ^N)`. -/
def IsBalanced (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ)) : Prop :=
  V Finset.univ = piV 𝒞 V (coal Finset.univ)

end FuzzyGames.NTUCore
