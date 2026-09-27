import Mathlib
import Definitions.Def_FoundationsML_DimReduction_SqNorm

namespace FoundationsML.DimReduction

/-- Lemma 15.4 (Johnson-Lindenstrauss; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 355, PDF p. 372 — this mission's goal). For any
`0 < ε < 1/2` and any integer `m > 4`, let `k = ⌈20 log(m)/ε²⌉`. Then for any set `V` of `m`
points in `ℝ^N`, there exists a map `f : ℝ^N → ℝ^k` such that for all `u, v ∈ V`,
`(1−ε)‖u−v‖² ≤ ‖f(u)−f(v)‖² ≤ (1+ε)‖u−v‖²`.

**Formalization Note.** The book's `k = 20 log(m)/ε²` is a real number in general; since the
target dimension of a map into `ℝ^k` must be a natural number, `k` is taken to be
`⌈20 log(m)/ε²⌉` (`Nat.ceil`), which only strengthens the book's own success-probability
argument (rounding up the number of dimensions can only decrease the failure probability of
each pair in the union bound the book's proof uses), so the existential conclusion is no
weaker than the book's. The statement is a bare existential, matching the book's own "there
exists a map `f`" exactly — not a universally-quantified probabilistic claim about a specific
random construction, which is what Lemma 15.3 (not this lemma) states. -/
theorem johnson_lindenstrauss {N : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (m : ℕ) (hm : 4 < m) (V : Finset (Fin N → ℝ)) (hV : V.card = m) :
    ∃ f : (Fin N → ℝ) → (Fin ⌈20 * Real.log (m : ℝ) / ε ^ 2⌉₊ → ℝ),
      ∀ u ∈ V, ∀ v ∈ V,
        (1 - ε) * SqNorm (u - v) ≤ SqNorm (f u - f v) ∧
          SqNorm (f u - f v) ≤ (1 + ε) * SqNorm (u - v) := by sorry

end FoundationsML.DimReduction

