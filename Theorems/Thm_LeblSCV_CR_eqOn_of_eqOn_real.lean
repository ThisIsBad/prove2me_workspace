import Mathlib
import Definitions.Def_LeblSCV_CR_realEmbed

namespace LeblSCV.CR

/-- Lemma 3.1.2 (Lebl, p. 104): let `ℝⁿ ⊂ ℂⁿ` be the natural inclusion and `V ⊂ ℂⁿ` a domain with
`V ∩ ℝⁿ ≠ ∅`. If `f, g` are holomorphic on `V` and `f = g` on `V ∩ ℝⁿ`, then `f = g` on `V`. -/
theorem eqOn_of_eqOn_real {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVR : (V ∩ Set.range (realEmbed (n := n))).Nonempty) (f g : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (hfg : ∀ z ∈ V ∩ Set.range (realEmbed (n := n)), f z = g z) :
    Set.EqOn f g V := by sorry

end LeblSCV.CR
