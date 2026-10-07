import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_COP

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

/-! # Facial descriptions and small facial descriptions

Karp & Papadimitriou, MIT/LCS/TM-154 (Feb. 1980), §2, pp. 4–5. -/

/-- A set of triples `⟨z, f, g⟩` with `z ∈ {0,1}*`, `f ∈ ℤⁿ⁽ᶻ⁾` and `g ∈ ℤ`. -/
abbrev Triples (C : COP) : Type := Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)

/-- **Facial description** (p. 4). `F` is a facial description of `C` if (i) every triple
`⟨z, f, g⟩ ∈ F` has `z ∈ L`, and (ii) for each `z ∈ L` and every `x ∈ ℚⁿ⁽ᶻ⁾`,
`x ∈ CH(S(z))` iff `f · x ≤ g` for every triple `⟨z, f, g⟩ ∈ F`. -/
def IsFacialDescription (C : COP) (F : Triples C) : Prop :=
  (∀ t ∈ F, t.1 ∈ C.L) ∧
    ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
      x ∈ hull C z ↔
        ∀ (f : Fin (C.n z) → ℤ) (g : ℤ), (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
          (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)

/-- **Small** (p. 5). There is a polynomial, here `m ↦ m ^ k + k`, such that for every triple
`⟨z, f, g⟩ ∈ F` each component of `f` and `g` has absolute value at most `2 ^ p(|z| + n(z))`. -/
def IsSmall (C : COP) (F : Triples C) : Prop :=
  ∃ k : ℕ, ∀ t ∈ F,
    (∀ i, |t.2.1 i| ≤ (2 : ℤ) ^ ((t.1.length + C.n t.1) ^ k + k)) ∧
      |t.2.2| ≤ (2 : ℤ) ^ ((t.1.length + C.n t.1) ^ k + k)

/-- The language of codes `⟨z, f, g⟩` of the triples of `F`; "`F(C) ∈ NP`" means that this
language is in `NP`. -/
def tripleLang (C : COP) (F : Triples C) : Lang BSym :=
  {w | ∃ t ∈ F, w = encTriple t.1 t.2.1 t.2.2}

end KarpPapadimitriou.Facial
