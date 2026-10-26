import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.ThreeBuffer

/-- The three-buffer two-station reentrant line of Figure 1 (p. 120): route `1 → 2 → 1`, i.e.
classes 1 and 3 at station 1 and class 2 at station 2. In 0-based indices: classes `0, 2` at
station `0`, class `1` at station `1`; `m` is the vector of mean service times `(m₁, m₂, m₃)`. -/
def threeBuffer (m : Fin 3 → ℝ) : ReentrantLine 2 3 := ⟨![0, 1, 0], m⟩

/-- `Q_k⁺(t) = ∑_{l ≤ k} Q_l(t)` (2.2), for any number `K` of classes (0-based). -/
noncomputable def Qplus {K : ℕ} (Q : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (· ≤ k), Q t l

/-- The constant `θ = m₁ / (m₁ + m₃)` of the proof of Theorem 3.1 (p. 121). -/
noncomputable def theta (m : Fin 3 → ℝ) : ℝ := m 0 / (m 0 + m 2)

/-- The two linear Lyapunov components of the proof of Theorem 3.1 (p. 121), 0-based:
`lyap m Q 0 = G₁ = θ Q₁⁺ + (1 - θ) Q₃⁺` and `lyap m Q 1 = G₂ = Q₂⁺`. -/
noncomputable def lyap (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) : Fin 2 → ℝ → ℝ :=
  ![fun t => theta m * Qplus Q 0 t + (1 - theta m) * Qplus Q 2 t, fun t => Qplus Q 1 t]

end DaiWeissFluid.ThreeBuffer
