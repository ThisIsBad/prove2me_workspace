import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `φ(ξ) = l.u.b._{x ∈ G} (Σxξ − f(x))`. Meaningful only for `ξ`
in `conjDomain G f`; the real `sSup` returns `0` on an unbounded (or empty) set, so every
statement evaluates `conjFun G f` only on `conjDomain G f`. -/
noncomputable def conjFun {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  sSup ((fun x => x ⬝ᵥ ξ - f x) '' G)

end ConjugateConvex.Involution
