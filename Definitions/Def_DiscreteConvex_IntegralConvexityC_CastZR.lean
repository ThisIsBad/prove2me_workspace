import Mathlib

/-!
Casting an integer-valued function `Zⁿ → Z ∪ {+∞}` into a real-valued one `Zⁿ → R ∪ {+∞}`
(Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Proposition 3.30's `f : Zⁿ → Z∪{+∞}`), in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The cast `(Zⁿ → Z∪\{+∞\}) → (Zⁿ → R∪\{+∞\})`. -/
def CastZR {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => WithTop.map (fun z : ℤ => (z : ℝ)) (f x)

end DiscreteConvex.IntegralConvexityC
