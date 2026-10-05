import Mathlib

namespace BertsekasShreve.FiniteHorizon

open scoped ENNReal

/-- Addition in `R*` with the book's convention `∞ − ∞ = −∞ + ∞ = ∞` (Section 2.1, item (6),
p. 26). It differs from `EReal`'s `+`, where `⊥ + ⊤ = ⊥`, only on that pair. -/
noncomputable def badd (a b : EReal) : EReal := if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

/-- Expected value with respect to a probability distribution `p` on a countable set `W`
(Section 2.3.2, p. 31): `E{z(w)} = ∑ p(w) z⁺(w) − ∑ p(w) z⁻(w)`, with
`z⁺ = max{0, z}`, `z⁻ = max{0, −z}` and the convention `∞ − ∞ = ∞`. -/
noncomputable def expect {W : Type*} (p : PMF W) (z : W → EReal) : EReal :=
  let P : ℝ≥0∞ := ∑' w, p w * (z w).toENNReal
  let Q : ℝ≥0∞ := ∑' w, p w * (-(z w)).toENNReal
  if P = ⊤ then ⊤ else (P : EReal) - (Q : EReal)

/-- The mapping of the multiplicative cost model, eq. (26) of Chapter 2 (Section 2.3.4,
p. 37) = eq. (33) of Chapter 3:
`H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}`, where `w` ranges over a countable set `W`
with probability distribution `p(· | x, u)`, `g : S C W → R*` and `f : S C W → S`. -/
noncomputable def multiplicativeH {S C W : Type*} (p : S → C → PMF W)
    (g : S → C → W → EReal) (f : S → C → W → S) : S → C → (S → EReal) → EReal :=
  fun x u J => expect (p x u) (fun w => g x u w * J (f x u w))

/-- The mapping of the minimax control model, eq. (29) of Chapter 2 (Section 2.3.5, p. 38) =
eq. (34) of Chapter 3:
`H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}`, where `W(x, u) ⊆ W`,
`g : S C W → [−∞, ∞]`, `f : S C W → S`, `α` a scalar, and the sum uses the book's
convention `∞ − ∞ = ∞` (`badd`). -/
noncomputable def minimaxH {S C W : Type*} (Wset : S → C → Set W) (g : S → C → W → EReal)
    (f : S → C → W → S) (α : ℝ) : S → C → (S → EReal) → EReal :=
  fun x u J => ⨆ w ∈ Wset x u, badd (g x u w) ((α : EReal) * J (f x u w))

end BertsekasShreve.FiniteHorizon
