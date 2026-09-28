import Mathlib

/-!
# Steuer–Choo (1983), §§2–3: weighted and augmented weighted Tchebycheff values, the sets `Φ(α)`

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §2, pp. 327–328, and §3, p. 330.

The weighted Tchebycheff program `min {α} s.t. α ≥ λᵢ(z*ᵢ − zᵢ), 1 ≤ i ≤ k, fᵢ(x) = zᵢ, x ∈ S`
has, for a fixed criterion vector `z`, minimal `α` equal to `maxᵢ λᵢ(z*ᵢ − zᵢ)`; `tcheb` is that value
and `augTcheb` adds the augmentation term `ρ eᵀ(z* − z)`. The program variable `α` is thereby
eliminated.
-/

namespace SteuerChoo.Discrete

/-- The weighted Tchebycheff value `maxᵢ λᵢ (z*ᵢ − zᵢ)`, the minimal `α` of the weighted Tchebycheff
program at the criterion vector `z` (§3, p. 330). -/
noncomputable def tcheb {k : ℕ} [NeZero k] (lam zstar z : Fin k → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => lam i * (zstar i - z i))

/-- The augmented weighted Tchebycheff value `maxᵢ λᵢ (z*ᵢ − zᵢ) + ρ eᵀ(z* − z)` (§2, p. 328; the
objective of the augmented weighted Tchebycheff program (3.5), p. 332, at `z` with minimal `α`). -/
noncomputable def augTcheb {k : ℕ} [NeZero k] (lam : Fin k → ℝ) (rho : ℝ) (zstar z : Fin k → ℝ) :
    ℝ :=
  tcheb lam zstar z + rho * ∑ i, (zstar i - z i)

/-- `Φ(α) = {z ∈ ℝᵏ | zᵢ ∈ [z*ᵢ − (α/λᵢ), +∞) when λᵢ > 0}` (§3, p. 330). -/
def Phi {k : ℕ} (lam zstar : Fin k → ℝ) (α : ℝ) : Set (Fin k → ℝ) :=
  {z | ∀ i, 0 < lam i → zstar i - α / lam i ≤ z i}

end SteuerChoo.Discrete
