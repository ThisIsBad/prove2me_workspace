import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

open MeasureTheory

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- The mapping `H(x, u, J) = g(x,u) + α ∫_S J(x′) t(dx′|x,u)` (p. 195), with the integral in the
extended sense (43) of Chapter 7 and the sum taken with the convention (42). -/
noncomputable def H (M : Model S C W) (J : S → EReal) (z : S × C) : EReal :=
  BertsekasShreve.FiniteHorizon.badd (M.g z) ((M.α : EReal) * extInt (fun h => ∫⁻ y, h y ∂(M.t z)) J)

/-- **Definition 8.4** (p. 194). For `μ ∈ U(C|S)` and universally measurable `J : S → R*`,
`T_μ(J)(x) = ∫_C [g(x,u) + α ∫_S J(x′) t(dx′|x,u)] μ(du|x)`. -/
noncomputable def Tmu (M : Model S C W) (μ : UCS M) (J : S → EReal) (x : S) : EReal :=
  extInt (fun h => ∫⁻ u, h u ∂(μ.1.toFun x)) (fun u => H M J (x, u))

/-- **Definition 8.5** (p. 195). For universally measurable `J : S → R*`,
`T(J)(x) = inf_{u ∈ U(x)} {g(x,u) + α ∫_S J(x′) t(dx′|x,u)}`. -/
noncomputable def T (M : Model S C W) (J : S → EReal) (x : S) : EReal :=
  ⨅ u ∈ M.U x, H M J (x, u)

/-- The identically zero function `J₀ : S → R*`. -/
noncomputable def J0 (S : Type*) : S → EReal := fun _ => 0

/-- The composition `T_{μ₀} T_{μ₁} ⋯ T_{μ_{K-1}}` (applied to `J`, the innermost operator being
`T_{μ_{K-1}}`) for a Markov policy `(μ₀, …, μ_{N-1})` and `K ≤ N`. -/
noncomputable def TmuComp (M : Model S C W) (ν : Fin M.N → UCS M) (K : ℕ) (J : S → EReal) :
    S → EReal :=
  ((List.finRange M.N).filter fun k : Fin M.N => (k : ℕ) < K).foldr (fun k J' => Tmu M (ν k) J') J

end BertsekasShreve.BorelFinite
