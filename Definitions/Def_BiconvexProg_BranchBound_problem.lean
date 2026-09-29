import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_BiconvexProg_BranchBound_Box

namespace BiconvexProg.BranchBound

variable {n : ℕ}

/-- The bilinear form `xᵀy = ∑ᵢ xᵢ yᵢ` on `ℝⁿ × ℝⁿ`. -/
def bilin (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, z.1 i * z.2 i

/-- The objective of Problem 𝒫 (p. 274): `φ(x, y) = f(x) + xᵀy + g(y)`. -/
def objective (f g : (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  f z.1 + bilin z + g z.2

/-- The node function of a box `B` (p. 276):
`ψ^B(x, y) = f(x) + Vex_B xᵀy + g(y)`, with `Vex_B` the convex envelope over the box. -/
noncomputable def nodeFun (f g : (Fin n → ℝ) → ℝ) (B : Box n)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  f z.1 + convexEnvelope B.toSet bilin z + g z.2

/-- The branching gap of coordinate `i` of box `B` at the point `z` (p. 277):
`x_i y_i − Vex_{B_i} x_i y_i`, the envelope taken over the `i`-th rectangle of `B`. -/
noncomputable def gap (B : Box n) (i : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  z.1 i * z.2 i - convexEnvelope (B.rect i) (fun p : ℝ × ℝ => p.1 * p.2) (z.1 i, z.2 i)

/-- The standing hypotheses of Problem 𝒫 (pp. 274, 276): the dimension `n` is positive; the box
`Ω` is nonempty (`l ≤ L`, `m ≤ M`); `f` and `g` are convex and continuous on
`{x : l ≤ x ≤ L}` and `{y : m ≤ y ≤ M}` respectively; `S` is closed and convex; and the feasible
set `S ∩ Ω` is nonempty. (Continuity of `f`, `g` is taken for granted in the paper.) -/
structure IsProblemP (S : Set ((Fin n → ℝ) × (Fin n → ℝ))) (f g : (Fin n → ℝ) → ℝ)
    (Ω : Box n) : Prop where
  pos_dim : 0 < n
  lL : Ω.l ≤ Ω.L
  mM : Ω.m ≤ Ω.M
  f_convex : ConvexOn ℝ (Set.Icc Ω.l Ω.L) f
  g_convex : ConvexOn ℝ (Set.Icc Ω.m Ω.M) g
  f_cont : ContinuousOn f (Set.Icc Ω.l Ω.L)
  g_cont : ContinuousOn g (Set.Icc Ω.m Ω.M)
  S_closed : IsClosed S
  S_convex : Convex ℝ S
  feasible : (S ∩ Ω.toSet).Nonempty

end BiconvexProg.BranchBound
