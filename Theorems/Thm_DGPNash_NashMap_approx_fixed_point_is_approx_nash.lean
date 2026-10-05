import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

/-- Lemma 3.8, p. 207: an approximate fixed point of Nash's map is an approximate Nash equilibrium. -/
theorem approx_fixed_point_is_approx_nash {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    IsApproxNash u x
      ((n : ℝ) * Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u)) *
        (1 + Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u))) *
        max (maxPayoff u) 1) := by sorry

end DGPNash.NashMap

