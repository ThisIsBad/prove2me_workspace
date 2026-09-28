import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension

/-- The linear perturbation `ω[p](x) = ω(x) + ⟨p, x⟩` (Murota 1996, p. 280, Eq. (2.7); written
`ω_p` in §3 and `g[p]` in Eq. (4.7)). A function on `B` is modelled as a total function
`(V → ℤ) → ℝ` of which only the values on `B` are ever used. -/
def perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ) : (V → ℤ) → ℝ :=
  fun x => ω x + pairing p (toReal x)

/-- The exchange property (EXC) of `ω : B → ℝ` (Murota 1996, p. 278, Eq. (2.4)): for `x, y ∈ B`
and `u ∈ supp⁺(x − y)` there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B`,
`y + χ_u − χ_v ∈ B` and `ω(x) + ω(y) ≤ ω(x − χ_u + χ_v) + ω(y + χ_u − χ_v)`.
A function satisfying (EXC) is called M-concave. -/
def SatisfiesEXC {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u : V, 0 < (x - y) u →
    ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B ∧
      ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v)

/-- The local exchange property (EXC_loc) (Murota 1996, p. 282, Eq. (3.1)): for `x, y ∈ B` with
`‖x − y‖ = ∑_v |x(v) − y(v)| = 4` there **exist** `u ∈ supp⁺(x − y)` and `v ∈ supp⁻(x − y)` with
`x − χ_u + χ_v ∈ B`, `y + χ_u − χ_v ∈ B` and
`ω(x) + ω(y) ≤ ω(x − χ_u + χ_v) + ω(y + χ_u − χ_v)`. -/
def SatisfiesEXCLoc {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∑ w, |x w - y w| = 4 →
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧
      y + chi u - chi v ∈ B ∧ ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v)

open Classical in
/-- `argmax(g) = {x ∈ B | g(x) ≥ g(y) ∀ y ∈ B}` (Murota 1996, p. 285, Eq. (4.5)). -/
noncomputable def argmaxB {V : Type*} (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) :
    Finset (V → ℤ) :=
  B.filter (fun x => ∀ y ∈ B, g y ≤ g x)

end SteinitzExchange.Extension
