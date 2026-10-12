import Mathlib

namespace HarrisContact.Extinction
open MeasureTheory
open scoped ENNReal NNReal

/-- Z_d: the d-dimensional integer lattice. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Ξ₀: the finite subsets of Z_d (the states of the chain of §4). -/
abbrev Config (d : ℕ) := Finset (Site d)

/-- N_x = {y : Σ_i |x^i − y^i| = 1}, enumerated inside the box Π_i [x^i − 1, x^i + 1]. -/
noncomputable def nbrs {d : ℕ} (x : Site d) : Config d :=
  (Fintype.piFinset fun i => Finset.Icc (x i - 1) (x i + 1)).filter (fun y => ∑ i, |x i - y i| = 1)

/-- ξ(N_x): the number of points of ξ among the neighbours of x. -/
noncomputable def occ {d : ℕ} (ξ : Config d) (x : Site d) : ℕ := (ξ ∩ nbrs x).card

/-- {x : x ∼ ξ}: sites outside ξ with a neighbour in ξ. -/
noncomputable def bdry {d : ℕ} (ξ : Config d) : Config d := ξ.biUnion nbrs \ ξ

/-- (4.4) q_ξ = μ|ξ| + Σ_{x∼ξ} λ_{ξ(N_x)}. -/
noncomputable def exitRate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : ℝ :=
  μ * ξ.card + ∑ x ∈ bdry ξ, lam (occ ξ x)

/-- (4.5) q_{ξη} for η ≠ ξ (0 except at the listed η). -/
noncomputable def rate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) : ℝ :=
  (∑ x ∈ ξ, if η = ξ.erase x then μ else 0) +
    ∑ x ∈ bdry ξ, if η = insert x ξ then lam (occ ξ x) else 0

/-- The states reachable from ξ in one jump. -/
noncomputable def succ {d : ℕ} (ξ : Config d) : Finset (Config d) :=
  ξ.image (fun x => ξ.erase x) ∪ (bdry ξ).image (fun x => insert x ξ)

/-- r(ξ, η), the imbedded jump chain; a state with q_ξ = 0 (e.g. ∅) is absorbing. -/
noncomputable def jump {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) : ℝ :=
  if exitRate μ lam ξ = 0 then (if η = ξ then 1 else 0) else rate μ lam ξ η / exitRate μ lam ξ

/-- r^{(n)}(ξ, η), the n-step transition matrix of the jump chain. -/
noncomputable def jumpPow {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : ℕ → Config d → Config d → ℝ
  | 0, ξ, η => if ξ = η then 1 else 0
  | n + 1, ξ, η => ∑ ζ ∈ insert ξ (succ ξ), jump μ lam ξ ζ * jumpPow μ lam n ζ η

/-- Feller's backward recursion: P^{(n)}_t(ξ, η) = probability of being at η at time t after at
most n jumps. -/
noncomputable def transN {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : ℕ → ℝ → Config d → Config d → ℝ≥0∞
  | 0, t, ξ, η => if ξ = η then ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) else 0
  | n + 1, t, ξ, η => transN μ lam 0 t ξ η +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η

/-- P_t(ξ, η): the minimal transition function of the rates (4.4)–(4.5). -/
noncomputable def trans {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ η : Config d) : ℝ≥0∞ :=
  ⨆ n, transN μ lam n t ξ η

/-- (5.1) p_t(ξ) = P_ξ{ξ_t ≠ ∅}, as 1 − P_t(ξ, ∅). -/
noncomputable def surv {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  1 - trans μ lam t ξ ∅

/-- (5.1) p_∞(ξ), as the infimum over t ≥ 0 of p_t(ξ). -/
noncomputable def survInf {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, surv μ lam t ξ

/-- (4.6) m_t(ξ) = 𝓔_ξ |ξ_t|. -/
noncomputable def meanSize {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ∑' η : Config d, trans μ lam t ξ η * (η.card : ℝ≥0∞)

end HarrisContact.Extinction
