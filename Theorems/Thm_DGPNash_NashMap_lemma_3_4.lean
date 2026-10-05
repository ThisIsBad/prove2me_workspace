import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

/-- Lemma 3.4, p. 205: Nash's map has the paper's explicit Lipschitz constant. -/
theorem lemma_3_4 {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x x' : Fin r → Fin n → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x')
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ p j, |x p j - x' p j| ≤ δ) :
    ∀ p j, |nashMap u x p j - nashMap u x' p j| ≤
      (1 + 2 * maxPayoff u * (r : ℝ) * (n : ℝ) * ((n : ℝ) + 1)) * δ := by sorry

end DGPNash.NashMap

