import Mathlib

namespace SPOBounds.Margin

/-- `w` is an optimization oracle for the feasible region `S` (arXiv:1905.11488v3, p. 5):
for every cost vector `c` (a continuous linear functional, so `cᵀv` is `c v`), `w c` lies in
`S` and minimizes `v ↦ c v` over `S`. No tie-breaking rule is imposed. -/
def IsOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) : Prop :=
  ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ v ∈ S, c (w c) ≤ c v

/-- The SPO loss `ℓ_SPO(ĉ, c) = cᵀ w*(ĉ) − cᵀ w*(c)` of the oracle `w` (p. 6). -/
noncomputable def spoLoss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : StrongDual ℝ E → E) (chat c : StrongDual ℝ E) : ℝ :=
  c (w chat) - c (w c)

/-- The linear optimization gap `ω_S(c) = max_{w ∈ S} cᵀw − min_{w ∈ S} cᵀw` (p. 8), written
with `sSup`/`sInf` of the image `c '' S` (attained for nonempty compact `S`). -/
noncomputable def omega {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (c : StrongDual ℝ E) : ℝ :=
  sSup ((fun v => c v) '' S) - sInf ((fun v => c v) '' S)

/-- `ω_S(𝒞) = sup_{c ∈ 𝒞} ω_S(c)` (p. 8). Used only for nonempty bounded `C`. -/
noncomputable def omegaSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (C : Set (StrongDual ℝ E)) : ℝ :=
  sSup (omega S '' C)

/-- `ρ(𝒞) = sup_{c ∈ 𝒞} ‖c‖_*` (p. 19; `ρ₂(𝒞)` in the ℓ₂ set-up, where the dual norm is the
Euclidean norm). The norm of a continuous linear functional is its operator norm, i.e. the dual
norm. Used only for nonempty bounded `C`. -/
noncomputable def rhoSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (StrongDual ℝ E)) : ℝ :=
  sSup ((fun c => ‖c‖) '' C)

end SPOBounds.Margin
