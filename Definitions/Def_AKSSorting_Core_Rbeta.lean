import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain

namespace AKSSorting.Core

variable {α : Type} [LinearOrder α]

/-- `A^{-β}` (Ajtai–Komlós–Szemerédi 1983, Definition 8.1, p. 13): writing
`A = {a₀ < a₁ < ⋯ < a_m}`, `A^{-β} = {a_{[β]}, a_{[β]+1}, …, a_{m-[β]}}`, i.e. `A` with its `[β]`
smallest and `[β]` largest elements removed (`[β] = ⌊β⌋`). An element `a ∈ A` has index
`#{b ∈ A | b < a}`; it is kept iff `[β] ≤ index` and `index ≤ m - [β]`, i.e.
`index + [β] + 1 ≤ |A|`. -/
noncomputable def trimmed (β : ℝ) (A : Finset α) : Finset α :=
  A.filter fun a =>
    ⌊β⌋₊ ≤ (A.filter fun b => b < a).card ∧ (A.filter fun b => b < a).card + ⌊β⌋₊ + 1 ≤ A.card

/-- `R^β_G(t₁, t₂)` (Definition 8.1, p. 13): for a position `G`, a chain `C` and nodes `t₁, t₂`,
every element of `Cont_G(C(t₁))^{-β}` is smaller than every element of `Cont_G(C(t₂))^{-β}`,
where `Cont_G(X) = G(X)` is the set of contents of the registers in `X`. -/
def Rbeta {R : Type} [DecidableEq R] {i : ℕ} (G : R → α) (C : Fin (2 ^ i) → Finset R) (β : ℝ)
    (t₁ t₂ : Fin (2 ^ i)) : Prop :=
  ∀ x ∈ trimmed β ((C t₁).image G), ∀ y ∈ trimmed β ((C t₂).image G), x < y

end AKSSorting.Core
