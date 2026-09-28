import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
The SET COVERING I input of Fig. 1 (Johnson 1974, p. 265), for a given `k`.

`T` consists of `k · k!` points, divided into `k` segments of `k!` points each. The point
`(s, q)` is point `q` (`0 ≤ q < k!`) of segment `s + 1` (`0 ≤ s < k`).
-/

/-- The `k · k!` points of `T`: segment `s + 1` (`s : Fin k`), position `q` (`q : Fin k!`). -/
abbrev Fig1Point (k : ℕ) := Fin k × Fin k.factorial

/-- Indices of the sets of `F`: `inl q` for the `k!` sets of `F₀`, and `inr ⟨s, b⟩` for the
`k!/(s+1)` sets of `F₁` covering segment `s + 1`, `b < k!/(s+1)`. -/
abbrev Fig1Index (k : ℕ) := Fin k.factorial ⊕ (Σ s : Fin k, Fin (k.factorial / (s.val + 1)))

/-- The family `F` of Fig. 1.
* `F₀`: the set `inl q` contains one point from each segment, the point `q`; these `k!` sets
  are disjoint and have `k` elements.
* `F₁`: the set `inr ⟨s, b⟩` is the block of the `s + 1` points `q` of segment `s + 1` with
  `⌊q / (s+1)⌋ = b`; for fixed `s` these are `k!/(s+1)` disjoint `(s+1)`-element sets covering
  segment `s + 1`. -/
def fig1 (k : ℕ) : Fig1Index k → Finset (Fig1Point k)
  | Sum.inl q => Finset.univ.filter (fun x => x.2 = q)
  | Sum.inr ⟨s, b⟩ => Finset.univ.filter (fun x => x.1 = s ∧ x.2.val / (s.val + 1) = b.val)

/-- The subfamily `F₁` of Fig. 1: all the sets `inr ⟨s, b⟩`. -/
def fig1F₁ (k : ℕ) : Finset (Finset (Fig1Point k)) :=
  Finset.univ.image (fun i : (Σ s : Fin k, Fin (k.factorial / (s.val + 1))) => fig1 k (Sum.inr i))

/-- The subfamily `F₀` of Fig. 1: all the sets `inl q`. -/
def fig1F₀ (k : ℕ) : Finset (Finset (Fig1Point k)) :=
  Finset.univ.image (fun q : Fin k.factorial => fig1 k (Sum.inl q))

end JohnsonApprox.SetCover
