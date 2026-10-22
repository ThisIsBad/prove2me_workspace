import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

namespace FuzzyGames.Walras

open Set Pointwise

/-- The inner product `p · y = ∑ₖ pₖ yₖ` on `ℝ^l` (§4 (3)). -/
def dot {l : ℕ} (p y : Fin l → ℝ) : ℝ := ∑ k, p k * y k

/-- An exchange economy with `n` consumers and `l` commodities (§4, p. 5).
`pref i x y` reads `x ≽_i y` (consumer `i` weakly prefers `x` to `y`); `Y i` is the set
`Y(i) ⊂ ℝ^l` of initial endowments of consumer `i`. Every consumption set is `ℝ^l_+`. -/
structure Economy (n l : ℕ) where
  pref : Fin n → (Fin l → ℝ) → (Fin l → ℝ) → Prop
  Y : Fin n → Set (Fin l → ℝ)

variable {n l : ℕ}

/-- The strict preference `x ≻_i y`: `x ≽_i y` and not `y ≽_i x`. -/
def Economy.spref (E : Economy n l) (i : Fin n) (x y : Fin l → ℝ) : Prop :=
  E.pref i x y ∧ ¬ E.pref i y x

/-- The paper's standing assumptions of §4 together with assumption §4 (1).
* `Y(i)` is closed, convex and comprehensive (`Y(i) = Y(i) − ℝ^l_+`);
* `≽_i` is a preference preordering on `ℝ^l_+`: reflexive, transitive and complete;
* continuity: the upper and lower contour sets of `≽_i` in `ℝ^l_+` are closed;
* convexity: the upper contour sets of `≽_i` in `ℝ^l_+` are convex, and
  `x ≻_i y ⇒ αx + (1 − α)y ≻_i y` for `α ∈ ]0,1[` (the printed (1)(i) has `x ≽ y` in the
  premise, which is unsatisfiable at `x = y`; we read it with `x ≻ y`);
* (1)(ii) no consumer is satiated;
* (1)(iii) `Y(i)` meets the open positive orthant. -/
structure Economy.Assumptions (E : Economy n l) : Prop where
  closed_Y : ∀ i, IsClosed (E.Y i)
  convex_Y : ∀ i, Convex ℝ (E.Y i)
  comprehensive_Y : ∀ i, ∀ y ∈ E.Y i, ∀ z : Fin l → ℝ, 0 ≤ z → y - z ∈ E.Y i
  refl : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → E.pref i x x
  trans : ∀ i, ∀ x y z : Fin l → ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
    E.pref i x y → E.pref i y z → E.pref i x z
  total : ∀ i, ∀ x y : Fin l → ℝ, 0 ≤ x → 0 ≤ y → E.pref i x y ∨ E.pref i y x
  closed_upper : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → IsClosed {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i y x}
  closed_lower : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → IsClosed {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i x y}
  convex_upper : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → Convex ℝ {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i y x}
  strict_convex : ∀ i, ∀ x y : Fin l → ℝ, 0 ≤ x → 0 ≤ y → E.spref i x y →
    ∀ α : ℝ, 0 < α → α < 1 → E.spref i (α • x + (1 - α) • y) y
  nonsatiation : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → ∃ y : Fin l → ℝ, 0 ≤ y ∧ E.spref i y x
  pos_endowed : ∀ i, ∃ y ∈ E.Y i, ∀ k, 0 < y k

/-- `Y(τ) = ∑ᵢ τᵢ Y(i)`, the endowments a fuzzy coalition `τ` puts at its disposal
(§4, p. 6); pointwise Minkowski sum of scaled sets. -/
def Economy.Ytau (E : Economy n l) (τ : Fin n → ℝ) : Set (Fin l → ℝ) :=
  ∑ i, τ i • E.Y i

/-- `X(τ)`, the allocations of the fuzzy coalition `τ` (§4 (2)): bundles `x_τ^i ∈ ℝ^l_+` for
the members `i ∈ A_τ = {i | τᵢ > 0}` with `∑ᵢ τᵢ x_τ^i ∈ Y(τ)`. The coordinates `x_τ^i` with
`τᵢ = 0` are dummies: they are multiplied by `0` and never compared. -/
def Economy.X (E : Economy n l) (τ : Fin n → ℝ) : Set (Fin n → Fin l → ℝ) :=
  {x | (∀ i, 0 < τ i → 0 ≤ x i) ∧ ∑ i, τ i • x i ∈ E.Ytau τ}

/-- The fuzzy core of the economy (§4, p. 6): allocations `x ∈ X(τ^N)` that no nonzero fuzzy
coalition `τ ∈ [0,1]^n` can improve upon, i.e. there is no `x_τ ∈ X(τ)` with
`x_τ^i ≻_i x^i` for every `i ∈ A_τ`. -/
def Economy.fuzzyCore (E : Economy n l) : Set (Fin n → Fin l → ℝ) :=
  {x | x ∈ E.X 1 ∧ ∀ τ ∈ FuzzyGames.NTUCore.cube n, τ ≠ 0 →
    ¬ ∃ xτ ∈ E.X τ, ∀ i, 0 < τ i → E.spref i (xτ i) (x i)}

/-- The income function `r_i(p) = sup_{y ∈ Y(i)} p · y` (§4 (3)), valued in `EReal`
(it is `+∞` when `p · y` is unbounded above on `Y(i)`). -/
noncomputable def Economy.income (E : Economy n l) (i : Fin n) (p : Fin l → ℝ) : EReal :=
  ⨆ y ∈ E.Y i, ((dot p y : ℝ) : EReal)

/-- The budget set `B_i(p) = {x ∈ ℝ^l_+ | p · x ≤ r_i(p)}` (§4, p. 6). -/
def Economy.budget (E : Economy n l) (i : Fin n) (p : Fin l → ℝ) : Set (Fin l → ℝ) :=
  {x | 0 ≤ x ∧ ((dot p x : ℝ) : EReal) ≤ E.income i p}

/-- The set of Walras equilibria (§4 (4)): allocations `x̄ ∈ X(τ^N)` for which some price
`p̄ ∈ ℝ^l` satisfies (i) `p̄ · x̄^i = r_i(p̄)` and (ii) `x̄^i ≽_i x` for every `x ∈ B_i(p̄)`,
for every consumer `i`. -/
def Economy.walras (E : Economy n l) : Set (Fin n → Fin l → ℝ) :=
  {x | x ∈ E.X 1 ∧ ∃ p : Fin l → ℝ,
    (∀ i, ((dot p (x i) : ℝ) : EReal) = E.income i p) ∧
    ∀ i, ∀ z ∈ E.budget i p, E.pref i (x i) z}

/-- The set `Q(i) = Y(i) − {x ∈ ℝ^l_+ | x ≻_i x̄^i}` of the proof of Theorem 4.1 (§4, p. 6). -/
def Economy.Q (E : Economy n l) (xbar : Fin n → Fin l → ℝ) (i : Fin n) :
    Set (Fin l → ℝ) :=
  E.Y i - {x | 0 ≤ x ∧ E.spref i x (xbar i)}

end FuzzyGames.Walras
