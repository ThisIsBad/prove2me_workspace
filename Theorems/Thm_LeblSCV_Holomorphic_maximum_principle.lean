import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn

namespace LeblSCV.Holomorphic

/-- Theorem 1.2.8 (Maximum principle, Lebl, p. 25). Let `U ⊆ ℂⁿ` be a domain and `f` holomorphic
on `U`. If `|f|` attains a local maximum (relative to `U`) at some `a ∈ U`, then `f ≡ f(a)` on `U`. -/
theorem maximum_principle {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hUc : IsConnected U)
    {f : (Fin n → ℂ) → ℂ} (hf : IsHolomorphicOn f U)
    {a : Fin n → ℂ} (ha : a ∈ U) (hmax : IsLocalMaxOn (fun z => ‖f z‖) U a) :
    ∀ z ∈ U, f z = f a := by sorry

end LeblSCV.Holomorphic
