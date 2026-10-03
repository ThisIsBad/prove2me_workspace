import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations

namespace ProcessingNetworks.PacketNetworks

/-- The real-vector realization of an integer schedule or configuration. -/
def realize {J : ℕ} (s : Fin J → ℕ) : Fin J → ℝ := fun j => (s j : ℝ)

/-- `⟨S⟩`, the convex hull of a finite schedule (or configuration) set, embedded in `ℝ^J_+`. -/
noncomputable def hullFinset {J : ℕ} (S : Finset (Fin J → ℕ)) : Set (Fin J → ℝ) :=
  convexHull ℝ (realize '' (S : Set (Fin J → ℕ)))

/-- `Λ`, the subcritical region of a packet network (Eq. 12.24): `λ ∈ ℝ^I_+` is subcritical if
there is an activity mix `ŝ ∈ ⟨S⟩` and a configuration mix `ĉ ∈ ⟨C⟩` with `Rŝ = λ` and `Aŝ < ĉ`
(componentwise). Named distinctly from mission II's `Subcriticality.subcriticalRegion` (same
letter `Λ` in the book, but a different LP built from this chapter's own discrete schedule
structure `S`, `A`, `C`, not the continuous-time static planning problem), per this chunk's own
`BRIEF.md` pitfall note. -/
def subcriticalRegion {I J K : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (cfg : LinkConfigData J K) : Set (Fin I → ℝ) :=
  {lam | (∀ i, 0 ≤ lam i) ∧ ∃ shat ∈ hullFinset S, ∃ chat ∈ hullFinset cfg.C,
    (R dat).mulVec shat = lam ∧ ∀ k, (cfg.A.mulVec shat) k < chat k}

end ProcessingNetworks.PacketNetworks
