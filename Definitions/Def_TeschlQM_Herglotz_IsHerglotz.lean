import Mathlib

namespace TeschlQM.Herglotz

/-- Teschl, p. 106, Sec. 3.4 (also p. 94, after (3.41)): with `ℂ₊ = {z ∈ ℂ | Im(z) > 0}`, a
**Herglotz function** is a holomorphic function `F : ℂ₊ → ℂ₊` mapping the upper half plane to
itself. `F` is given on all of `ℂ`; only its values on `ℂ₊` matter. "Into itself" is the open
half plane: `Im F(z) > 0` for every `z ∈ ℂ₊`. -/
def IsHerglotz (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧ ∀ z : ℂ, 0 < z.im → 0 < (F z).im

end TeschlQM.Herglotz
