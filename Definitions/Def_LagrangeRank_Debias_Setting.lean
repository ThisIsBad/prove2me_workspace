import Mathlib

namespace LagrangeRank.Debias

open MeasureTheory Matrix

/-- Max-row-sum norm of a matrix, `‖M‖∞ = maxᵢ ∑ⱼ |Mᵢⱼ|` (paper, p. 8). It is `0` when the
row type is empty. -/
noncomputable def rowSumNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  ((Finset.univ : Finset m).sup fun i => (∑ j, ‖M i j‖₊ : NNReal) : NNReal)

/-- The ℓ1 norm `∑ᵢ |vᵢ|` of a vector; equivalently the `∞`-norm of the `1 × d` row `vᵀ`. -/
noncomputable def l1Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, |v i|

/-- Gradient of `F : ℝ^d → ℝ`, coordinatewise: `(∇F(θ))ᵢ = DF(θ) eᵢ`. -/
noncomputable def grad {d : ℕ} (F : (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ F θ (Pi.single i 1)

/-- Hessian of `F : ℝ^d → ℝ`: `(∇²F(θ))ᵢₖ = ∂ₖ (∇F)ᵢ (θ)`. -/
noncomputable def hess {d : ℕ} (F : (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i k => fderiv ℝ (grad F) θ (Pi.single k 1) i

/-- The bordered matrix (3.6): `Σ = (H  g ; gᵀ  0)` on the index type `Fin d ⊕ Unit`. -/
def borderedHessian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ :=
  fromBlocks H (replicateCol Unit g) (replicateRow Unit g) 0

/-- The block formula of p. 16 for the estimated inverse of the bordered matrix, built from
an estimate `Om` of the inverse Hessian and a constraint gradient `g`, with
`s = gᵀ Om g`:
`Θ₁₁ = Om − Om g s⁻¹ gᵀ Om`, `Θ₁₂ = Om g s⁻¹`, lower-left block `Θ₁₂ᵀ` (as printed),
`Θ₂₂ = −s⁻¹`. (Lean's `0⁻¹ = 0` makes it total.) -/
noncomputable def thetaBlock {d : ℕ} (Om : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ :=
  let s : ℝ := g ⬝ᵥ (Om *ᵥ g)
  fromBlocks (Om - s⁻¹ • vecMulVec (Om *ᵥ g) (g ᵥ* Om))
    (replicateCol Unit (s⁻¹ • (Om *ᵥ g)))
    (replicateRow Unit (s⁻¹ • (Om *ᵥ g)))
    (fun _ _ => -s⁻¹)

/-- The Lagrangian debiased estimator (3.9): `θᵈ = θ̂ − Θ₁₁ ∇L(θ̂)`. -/
def debiased {d : ℕ} (thetaHat : Fin d → ℝ) (Th : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gradHat : Fin d → ℝ) : Fin d → ℝ :=
  thetaHat - Th.toBlocks₁₁ *ᵥ gradHat

/-- The multiplier `λ` of (3.8): the last coordinate of `Θ (−∇L(θ̂) ; −f(θ̂))`. -/
def lam {d : ℕ} (Th : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (gradHat : Fin d → ℝ)
    (fHat : ℝ) : ℝ :=
  (Th *ᵥ Sum.elim (-gradHat) (fun _ => -fHat)) (Sum.inr ())

/-- `Σ*₁₁ = E[∇²L(θ*)]` (p. 15), as an entrywise Bochner integral of the random Hessian. -/
noncomputable def sigmaStar11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (Lfun : Ω → (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∫ ω, hess (Lfun ω) θ a b ∂P

/-- The coordinate variance `[Θ₁₁ Σ₁₁ Θ₁₁ᵀ]ⱼⱼ` (Assumption 3.5, Theorem 3.1). -/
def studVar {d : ℕ} (Th11 S : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  (Th11 * S * Th11ᵀ) j j

/-- The pairwise variance `(eᵢ − eⱼ)ᵀ Θ₁₁ Σ₁₁ Θ₁₁ᵀ (eᵢ − eⱼ)` (Assumption 3.5, Theorem 3.1). -/
def studVarPair {d : ℕ} (Th11 S : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : ℝ :=
  (Pi.single i 1 - Pi.single j 1 : Fin d → ℝ) ⬝ᵥ
    ((Th11 * S * Th11ᵀ) *ᵥ (Pi.single i 1 - Pi.single j 1 : Fin d → ℝ))

/-- The three remainder vectors `J₁, J₂, J₃` of (A.1), on `Fin d ⊕ Unit`, for one realization:
`gL t` is `∇L(t)`, `H` is `∇²L(θ̂)`, `f` the constraint, `g` its gradient map,
`Th`/`Ts` the matrices `Θ̂`/`Θ*`, `th`/`ts` the points `θ̂`/`θ*`. -/
def remJ1 {d : ℕ} (Th Ts : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gL : (Fin d → ℝ) → Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin d → ℝ) (th ts : Fin d → ℝ) : Fin d ⊕ Unit → ℝ :=
  (Th - Ts) *ᵥ Sum.elim (-gL th + H *ᵥ (th - ts)) (fun _ => -f th + g th ⬝ᵥ (th - ts))

/-- `J₂` of (A.1). -/
def remJ2 {d : ℕ} (Ts : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gL : (Fin d → ℝ) → Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin d → ℝ) (th ts : Fin d → ℝ) : Fin d ⊕ Unit → ℝ :=
  Ts *ᵥ Sum.elim (gL ts - gL th + H *ᵥ (th - ts)) (fun _ => f ts - f th + g th ⬝ᵥ (th - ts))

/-- `J₃` of (A.1), with `Sig` the bordered matrix `Σ̂`. -/
def remJ3 {d : ℕ} (Th Sig : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (th ts : Fin d → ℝ) :
    Fin d ⊕ Unit → ℝ :=
  (1 - Th * Sig) *ᵥ Sum.elim (th - ts) (fun _ => 0)

/-- The debiased estimator (3.9) computed from the data of one realization: the loss `L`,
the constraint `f`, the inverse-Hessian estimate `Om` (`Ω̂`) and the initial estimator `th`
(`θ̂`), with `Θ̂ = thetaBlock Om (∇f(θ̂))`. -/
noncomputable def estThetaD {d : ℕ} (L f : (Fin d → ℝ) → ℝ) (Om : Matrix (Fin d) (Fin d) ℝ)
    (th : Fin d → ℝ) : Fin d → ℝ :=
  debiased th (thetaBlock Om (grad f th)) (grad L th)

/-- `Θ*₁₁`: the upper-left block of `Θ* = thetaBlock Ω* (∇f(θ*))` (the p. 16 formula applied
to `(Ω*, ∇f(θ*))`, as in the proof of Corollary 3.1, p. 43). -/
noncomputable def thetaStar11 {d : ℕ} (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (thetaBlock OmS (grad f ts)).toBlocks₁₁

/-- The coordinate variance `[Θ*₁₁ Σ*₁₁ Θ*₁₁ᵀ]ⱼⱼ` of Assumption 3.5 and Theorem 3.1, with
`Θ*₁₁ = thetaStar11 f Ω* θ*` and `Σ*₁₁ = E[∇²L(θ*)]`. -/
noncomputable def popVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (L : Ω → (Fin d → ℝ) → ℝ) (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) (j : Fin d) : ℝ :=
  studVar (thetaStar11 f OmS ts) (sigmaStar11 P L ts) j

/-- The pairwise variance `(eᵢ − eⱼ)ᵀ Θ*₁₁ Σ*₁₁ Θ*₁₁ᵀ (eᵢ − eⱼ)` of Assumption 3.5 and
Theorem 3.1. -/
noncomputable def popVarPair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (L : Ω → (Fin d → ℝ) → ℝ) (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) (i j : Fin d) : ℝ :=
  studVarPair (thetaStar11 f OmS ts) (sigmaStar11 P L ts) i j

open Filter Topology in
/-- Assumptions 3.1–3.4 (pp. 16–17) and the standing assumptions of §3.1.1 (pp. 13–14), for a
sequence of problems indexed by the sample size `n`, all on one probability space `(Ω, P)`.

Reading of `≲`: the constants `K c₁ c₂ c₃ L₁ L₂` are fixed (independent of `n`), and the random
bounds hold, with constant `K`, on events `E n` whose complements have probability tending
to `0`. The constraint-gradient norm `‖∇f‖∞` is read as the ℓ1 norm (the `∞`-norm of the row
`∇fᵀ`). -/
structure Assumptions {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (d : ℕ → ℕ)
    (L : (n : ℕ) → Ω → (Fin (d n) → ℝ) → ℝ) (f : (n : ℕ) → (Fin (d n) → ℝ) → ℝ)
    (thetaStar : (n : ℕ) → Fin (d n) → ℝ) (thetaHat : (n : ℕ) → Ω → Fin (d n) → ℝ)
    (OmegaHat : (n : ℕ) → Ω → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (OmegaStar : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (r1 r2 r3 r4 r5 : ℕ → ℝ) (K c1 c2 c3 L1 L2 : ℝ) (E : ℕ → Set Ω) : Prop where
  /-- The loss is twice and the constraint once continuously differentiable. -/
  smooth_L : ∀ n ω, ContDiff ℝ 2 (L n ω)
  smooth_f : ∀ n, ContDiff ℝ 1 (f n)
  /-- Standing assumption (p. 14): `θ* ∈ C` and `θ̂ ∈ C`, where `C = {θ : f(θ) = 0}`. -/
  feasible_star : ∀ n, f n (thetaStar n) = 0
  feasible_hat : ∀ n ω, f n (thetaHat n ω) = 0
  /-- The rates are nonnegative. -/
  rates_nonneg : ∀ n, 0 ≤ r1 n ∧ 0 ≤ r2 n ∧ 0 ≤ r3 n ∧ 0 ≤ r4 n ∧ 0 ≤ r5 n
  c3_pos : 0 < c3
  /-- The good events have probability tending to one. -/
  events : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0)
  /-- Assumption 3.1: `‖θ̂ − θ*‖∞ ≲ r₁`. -/
  a31 : ∀ n, ∀ ω ∈ E n, ‖thetaHat n ω - thetaStar n‖ ≤ K * r1 n
  /-- Assumption 3.2, first part: `‖∇L(θ*)‖∞ ≲ r₂`. -/
  a32_grad : ∀ n, ∀ ω ∈ E n, ‖grad (L n ω) (thetaStar n)‖ ≤ K * r2 n
  /-- Assumption 3.2, second part: `‖∇²L(θ) − ∇²L(θ*)‖∞ ≤ L₁‖θ − θ*‖∞` on the segment
  `θ = θ* + t(θ̂ − θ*)`, `t ∈ [0, 1]`. -/
  a32_lip : ∀ n, ∀ ω ∈ E n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    rowSumNorm (hess (L n ω) (thetaStar n + t • (thetaHat n ω - thetaStar n))
        - hess (L n ω) (thetaStar n))
      ≤ L1 * ‖(thetaStar n + t • (thetaHat n ω - thetaStar n)) - thetaStar n‖
  /-- Assumption 3.3, first part: `‖∇f(θ*)‖ ≲ c₁` (ℓ1 reading). -/
  a33_grad : ∀ n, l1Norm (grad (f n) (thetaStar n)) ≤ c1
  /-- Assumption 3.3, second part: `‖∇f(θ) − ∇f(θ*)‖ ≤ L₂‖θ − θ*‖∞` on the segment (ℓ1 reading). -/
  a33_lip : ∀ n, ∀ ω ∈ E n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    l1Norm (grad (f n) (thetaStar n + t • (thetaHat n ω - thetaStar n))
        - grad (f n) (thetaStar n))
      ≤ L2 * ‖(thetaStar n + t • (thetaHat n ω - thetaStar n)) - thetaStar n‖
  /-- Assumption 3.4: `‖I − Ω̂∇²L(θ̂)‖∞ ≲ r₃`. -/
  a34_r3 : ∀ n, ∀ ω ∈ E n,
    rowSumNorm (1 - OmegaHat n ω * hess (L n ω) (thetaHat n ω)) ≤ K * r3 n
  /-- Assumption 3.4: `‖Ω̂ − Ω*‖∞ ≲ r₄`. -/
  a34_r4 : ∀ n, ∀ ω ∈ E n, rowSumNorm (OmegaHat n ω - OmegaStar n) ≤ K * r4 n
  /-- Assumption 3.4: `‖Ω*‖∞ ≲ c₂`. -/
  a34_c2 : ∀ n, rowSumNorm (OmegaStar n) ≤ c2
  /-- Assumption 3.4: `∇f(θ*)ᵀΩ*∇f(θ*) ≳ c₃`. -/
  a34_c3 : ∀ n, c3 ≤ grad (f n) (thetaStar n) ⬝ᵥ (OmegaStar n *ᵥ grad (f n) (thetaStar n))
  /-- Assumption 3.4: `‖Θ*‖∞ ≲ r₅`, for the whole bordered matrix `Θ*`. -/
  a34_r5 : ∀ n, rowSumNorm (thetaBlock (OmegaStar n) (grad (f n) (thetaStar n))) ≤ K * r5 n

end LagrangeRank.Debias
