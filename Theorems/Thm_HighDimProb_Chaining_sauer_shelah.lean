import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim

namespace HighDimProb.Chaining

/-- **Theorem 8.3.16** (Sauer-Shelah Lemma), Vershynin, *High-Dimensional Probability* (2018),
p. 205 (PDF p. 213).

"Let `F` be a class of Boolean functions on an `n`-point set `Ω`. Then `|F| ≤ ∑_{k=0}^d (n choose
k) ≤ (en/d)^d` where `d = vc(F)`." Here `Ω` is a finite type (the "`n`-point set", `n :=
Fintype.card Ω`), `F` a `Finset` of Boolean functions on `Ω` (automatically finite since `Ω →
Bool` is finite), and `d := (vcDim (F : Set (Ω → Bool))).toNat`: `vcDim` is always finite here
since every shattered `Λ ⊆ Ω` has `Λ.encard ≤ (Fintype.card Ω : ℕ∞) < ⊤`, so `toNat` recovers the
same natural number the book calls `d` without any extra finiteness hypothesis. At `d = 0` the
second bound's `en/d` divides by zero (Lean's convention `x / 0 = 0`), but the exponent `d = 0`
still forces `(en/d)^0 = 1` regardless (Lean's convention `x^0 = 1`), which is exactly the correct
non-vacuous bound `|F| ≤ 1` at VC dimension `0` (footnote-free, since the book's own proof of the
second inequality goes through the binomial-sum bound of Exercise 0.0.5, valid at `d = 0` too). -/
theorem sauer_shelah {Ω : Type} [Fintype Ω] (F : Finset (Ω → Bool)) :
    (F.card : ℝ) ≤
        ∑ k ∈ Finset.range ((vcDim (F : Set (Ω → Bool))).toNat + 1),
          ((Fintype.card Ω).choose k : ℝ) ∧
      (F.card : ℝ) ≤
        (Real.exp 1 * (Fintype.card Ω : ℝ) / (vcDim (F : Set (Ω → Bool))).toNat) ^
          (vcDim (F : Set (Ω → Bool))).toNat := by sorry

end HighDimProb.Chaining

