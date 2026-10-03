import Mathlib

open ComplexConjugate

namespace LeblSCV.CR

/-- Lemma 3.1.4 (Lebl, p. 106): let `V ⊂ ℂⁿ × ℂⁿ` be a domain, with coordinates `(z, ζ)`, let
`D = {(z, ζ) : ζ = z̄}` and suppose `D ∩ V ≠ ∅`. If `f, g` are holomorphic on `V` and `f = g` on
`D ∩ V`, then `f = g` on all of `V`. -/
theorem eqOn_of_eqOn_diagonal {n : ℕ} (V : Set ((Fin n → ℂ) × (Fin n → ℂ))) (hV : IsOpen V)
    (hVc : IsConnected V)
    (hDV : ({x | x.2 = fun k => conj (x.1 k)} ∩ V).Nonempty)
    (f g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f V)
    (hg : DifferentiableOn ℂ g V)
    (hfg : ∀ x ∈ {x : (Fin n → ℂ) × (Fin n → ℂ) | x.2 = fun k => conj (x.1 k)} ∩ V,
      f x = g x) :
    Set.EqOn f g V := by sorry

end LeblSCV.CR
