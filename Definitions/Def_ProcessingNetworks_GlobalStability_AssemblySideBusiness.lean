import Mathlib

namespace ProcessingNetworks.GlobalStability

/-- The fluid model of the "assembly with complementary side business" SPN of Figure 5.5, Dai &
Harrison p. 150 (PDF p. 166): two buffers with external arrival rates `lam1`, `lam2`; server 1
performs assembly (one activity consuming a unit from each buffer, mean time `m1`); server 2
processes buffer-2 units alone for direct sale (mean time `m2`). This SPN has a genuinely
multi-input activity that Chapter 2's "unitary network" vocabulary (one activity per buffer) does
not cover, so it is restated locally via its already-derived additional fluid equations
(8.36)-(8.39) (obtained, the book notes, "using the proof techniques in Chapter 7" — not
re-derived here), on top of the base fluid equations (6.1)-(6.6) for this SPN: `Ta`, `Ts` are the
cumulative service efforts of the assembly and side-sale activities (nondecreasing from `0`,
`1`-Lipschitz by the capacity bound (6.6) with single servers), the completions are `Ta/m1` and
`Ts/m2` (6.4), and the buffer contents obey `Z1 = Z1(0) + λ1 t - Ta/m1`,
`Z2 = Z2(0) + λ2 t - Ta/m1 - Ts/m2` (6.1)/(6.3) with `Z ≥ 0` (6.2). -/
def AssemblySideBusinessFluidModel (lam1 lam2 m1 m2 : ℝ) (Z1 Z2 Ta Ts : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Z1 t = Z1 0 + lam1 * t - Ta t / m1) ∧
  (∀ t : ℝ, 0 ≤ t → Z2 t = Z2 0 + lam2 * t - Ta t / m1 - Ts t / m2) ∧
  (Ta 0 = 0 ∧ Ts 0 = 0) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ Ta t - Ta s ∧ Ta t - Ta s ≤ t - s) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ Ts t - Ts s ∧ Ts t - Ts s ≤ t - s) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ Z1 t ∧ 0 ≤ Z2 t) ∧
  (∀ t : ℝ, 0 < t → Z2 t < Z1 t →
    ∀ d1 d2 : ℝ, HasDerivAt Z1 d1 t → HasDerivAt Z2 d2 t → d1 - d2 = lam1 - lam2) ∧
  (∀ t : ℝ, 0 < t → Z1 t < Z2 t →
    ∀ d1 d2 : ℝ, HasDerivAt Z1 d1 t → HasDerivAt Z2 d2 t → d1 - d2 = lam1 + 1 / m2 - lam2) ∧
  (∀ t : ℝ, 0 < t → 0 < Z1 t → 0 < Z2 t → ∀ d1 : ℝ, HasDerivAt Z1 d1 t → d1 = lam1 - 1 / m1) ∧
  (∀ t : ℝ, 0 < t → ∀ d1 : ℝ, HasDerivAt Z1 d1 t → d1 ≤ lam1)

/-- Definition 6.3 (fluid model stability), specialized to the assembly-with-side-business fluid
model. -/
def AssemblySideBusinessFluidStable (lam1 lam2 m1 m2 : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ Z1 Z2 Ta Ts : ℝ → ℝ,
    AssemblySideBusinessFluidModel lam1 lam2 m1 m2 Z1 Z2 Ta Ts →
    ∀ t : ℝ, γ * (Z1 0 + Z2 0) ≤ t → Z1 t = 0 ∧ Z2 t = 0

end ProcessingNetworks.GlobalStability
