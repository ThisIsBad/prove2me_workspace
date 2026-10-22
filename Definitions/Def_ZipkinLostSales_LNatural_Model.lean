import Mathlib

namespace ZipkinLostSales.LNatural

open MeasureTheory

/-!
# Zipkin (2008), §2–§3: the lost-sales recursion in the transformed state `v`, and L♮-convexity

Conventions (Zipkin, *On the Structure of Lost-Sales Inventory Models*, Oper. Res. 56 (2008),
pp. 937–939):

* `L : ℕ` is the lead time; states are `v : Fin L → ℝ`, indexed `0, …, L-1` as in the paper, and
  `vext v l` extends `v` by the paper's convention `v_L = 0` (and `0` beyond).
* Costs: `c` (procurement), `hh` (= ĥ, holding), `p` (lost-sales penalty), `γ` (discount factor).
* `μ : Measure ℝ` is the law of one period's demand `d` (data are stationary and the demands are
  independent, so one law serves every period).
* Time is indexed by the number of periods to go `k : ℕ`: `fbar … 0 = 0` is (2), and `gbar … k`
  is the paper's `ḡ_t` for the period `t` with `k + 1` periods to go, whose continuation is
  `fbar … k` (the paper's `f̄_{t+1}`); `fbar … (k+1) v = ⨅_{ζ ≤ 0} gbar … k v ζ` is (1). By
  stationarity "for all t" is "for all k".
* The paper's "min" is the infimum `⨅ ζ : Set.Iic (0:ℝ)`. Under nonnegative costs and nonnegative
  demand every term of `gbar` is `≥ 0` on `V`, so the infimum is over a set bounded below and is
  not Lean's junk value; this is not proved here.
* L♮-convexity (p. 938): `f : V → ℝ` is L♮-convex if `ψ(v, ζ) = f(v − ζe)`, `ζ ≤ 0`, is submodular
  on `V × ℜ⁻`. `LNatConvexOn D f` states this for a domain `D ⊆ ℝⁿ`, with the shift variable
  appended as the last coordinate of `Fin (n+1) → ℝ`.
-/

/-- The state space `V = {v ∈ ℝ^L : Jv ≥ 0}`: nonnegative vectors with nonincreasing components
(p. 938). -/
def V (L : ℕ) : Set (Fin L → ℝ) := {v | Antitone v ∧ ∀ l, 0 ≤ v l}

/-- `vext v l = v_l` for `l < L` and `0` otherwise (the paper's `v_L = 0`). -/
def vext {L : ℕ} (v : Fin L → ℝ) (l : ℕ) : ℝ := if h : l < L then v ⟨l, h⟩ else 0

/-- The transition of the transformed state (p. 938):
`v₊ = ([v₀ − v₁ − d]⁺ + v₁, v₂, …, v_{L−1}, 0) − ζe`, with `ζ = −z ≤ 0` the transformed order. -/
def next {L : ℕ} (v : Fin L → ℝ) (d ζ : ℝ) : Fin L → ℝ := fun l =>
  (if (l : ℕ) = 0 then max (vext v 0 - vext v 1 - d) 0 else 0) + vext v ((l : ℕ) + 1) - ζ

/-- The end-of-period holding-penalty cost `q̂(u) = ĥu⁺ + pu⁻` (p. 938). -/
def qhat (hh p u : ℝ) : ℝ := hh * max u 0 + p * max (-u) 0

/-- The expected one-period cost `q̂⁰(y) = E[q̂(y − d)]` for demand law `μ` (p. 938). -/
noncomputable def qhat0 (hh p : ℝ) (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ d, qhat hh p (y - d) ∂μ

/-- One step of the recursion (1) in the transformed state, for a continuation `F` (standing for
`f̄_{t+1}`): `−γ^L c ζ + q̂⁰(v₀ − v₁) + γ E[F(v₊)]`. This is `ĝ_t(Jv, −ζ)`, since `y = x₀ = v₀ − v₁`
and `z = −ζ`. -/
noncomputable def gstep {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (F : (Fin L → ℝ) → ℝ)
    (v : Fin L → ℝ) (ζ : ℝ) : ℝ :=
  -(γ ^ L * c * ζ) + qhat0 hh p μ (vext v 0 - vext v 1) + γ * ∫ d, F (next v d ζ) ∂μ

/-- The optimal cost `f̄(v)` with `k` periods to go: `fbar … 0 = 0` is (2), and
`fbar … (k+1) v = inf_{ζ ≤ 0} gstep (fbar … k) v ζ` is (1) (pp. 937–938). -/
noncomputable def fbar {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun v => ⨅ ζ : Set.Iic (0 : ℝ), gstep c hh p γ μ (fbar c hh p γ μ k) v ζ

/-- `ḡ(v, ζ)` with continuation `fbar … k`: the paper's `ḡ_t` for the period with `k + 1` periods
to go (p. 938). -/
noncomputable def gbar {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (k : ℕ) (v : Fin L → ℝ) (ζ : ℝ) :
    ℝ :=
  gstep c hh p γ μ (fbar c hh p γ μ k) v ζ

/-- Submodularity on a set `S ⊆ ℝⁿ` for the componentwise order:
`φ(x ⊔ y) + φ(x ⊓ y) ≤ φ(x) + φ(y)` for all `x, y ∈ S`. -/
def SubmodularOn {n : ℕ} (S : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, φ (x ⊔ y) + φ (x ⊓ y) ≤ φ x + φ y

/-- L♮-convexity on a domain `D ⊆ ℝⁿ` (p. 938): with `w = (x, ξ) ∈ ℝⁿ × ℝ`, the function
`(x, ξ) ↦ f(x − ξe)` is submodular on `{(x, ξ) : ξ ≤ 0, x ∈ D, x − ξe ∈ D}`, where `e` is the
all-ones vector. For `D = V` this set is `V × ℜ⁻`, the paper's definition. -/
def LNatConvexOn {n : ℕ} (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  SubmodularOn
    {w : Fin (n + 1) → ℝ | w (Fin.last n) ≤ 0 ∧ Fin.init w ∈ D ∧
      (fun i => Fin.init w i - w (Fin.last n)) ∈ D}
    (fun w => f (fun i => Fin.init w i - w (Fin.last n)))

/-- The domain `V × ℜ⁻` of functions `g(v, ζ)`, encoded in `Fin (L+1) → ℝ` with `ζ` the last
coordinate. -/
def VxNeg (L : ℕ) : Set (Fin (L + 1) → ℝ) :=
  {w | Fin.init w ∈ V L ∧ w (Fin.last L) ≤ 0}

/-- View `g : V × ℜ⁻ → ℝ` as a function on `Fin (L+1) → ℝ`, `ζ` being the last coordinate. -/
def liftG {L : ℕ} (g : (Fin L → ℝ) → ℝ → ℝ) (w : Fin (L + 1) → ℝ) : ℝ :=
  g (Fin.init w) (w (Fin.last L))

/-- `(v₊, v₂, …, v_{L−1}, 0) − ζe`, the next state of program (4) as a function of the decision
`v₊` (p. 939). -/
def next' {L : ℕ} (vplus : ℝ) (v : Fin L → ℝ) (ζ : ℝ) : Fin L → ℝ := fun l =>
  (if (l : ℕ) = 0 then vplus else vext v ((l : ℕ) + 1)) - ζ

/-- The objective of program (4) (p. 939), for a continuation `F` (standing for `f̄_{t+1}`):
`ψ(v₊, v, ζ) = ĥ(v₊ − v₁) + p(v₊ − v₀ + d) + γ F[(v₊, v₂, …, v_{L−1}, 0) − ζe]`. -/
def psi {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d vplus : ℝ) (v : Fin L → ℝ) (ζ : ℝ) : ℝ :=
  hh * (vplus - vext v 1) + p * (vplus - vext v 0 + d) + γ * F (next' vplus v ζ)

/-- The `v`-block of a point `w = (v₊, v₀, …, v_{L−1}, ζ) ∈ ℝ^{L+2}`. -/
def psiV {L : ℕ} (w : Fin (L + 2) → ℝ) : Fin L → ℝ := fun i => w i.succ.castSucc

/-- The domain of `ψ` in (4) (p. 939), as a subset of `ℝ^{L+2}` with coordinates ordered
`(v₊, v₀, …, v_{L−1}, ζ)`: `v ∈ V`, `ζ ≤ 0`, `−d ≤ v₊ − v₀ ≤ 0`, `v₊ − v₁ ≥ 0`. -/
def Dpsi (L : ℕ) (d : ℝ) : Set (Fin (L + 2) → ℝ) :=
  {w | psiV w ∈ V L ∧ w (Fin.last (L + 1)) ≤ 0 ∧ -d ≤ w 0 - vext (psiV w) 0 ∧
    w 0 - vext (psiV w) 0 ≤ 0 ∧ 0 ≤ w 0 - vext (psiV w) 1}

/-- `ψ` of (4) viewed as a function on `ℝ^{L+2}`, coordinates ordered `(v₊, v₀, …, v_{L−1}, ζ)`. -/
def liftPsi {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d : ℝ) (w : Fin (L + 2) → ℝ) : ℝ :=
  psi hh p γ F d (w 0) (psiV w) (w (Fin.last (L + 1)))

/-- `κ̄(v, ζ | d)`, program (4) (p. 939): the infimum of `ψ` over the constraint set
`−d ≤ v₊ − v₀ ≤ 0, v₊ − v₁ ≥ 0`, i.e. `v₊ ∈ [max (v₀ − d) v₁, v₀]`. This interval is nonempty when
`v ∈ V` and `d ≥ 0`; (3) is the same program before the substitution `v₊ = w + v₁`. -/
noncomputable def kappa {L : ℕ} (hh p γ : ℝ) (F : (Fin L → ℝ) → ℝ) (d : ℝ) (v : Fin L → ℝ)
    (ζ : ℝ) : ℝ :=
  ⨅ vplus : Set.Icc (max (vext v 0 - d) (vext v 1)) (vext v 0), psi hh p γ F d vplus v ζ

/-- `fbar … (k+1)` unfolds to the infimum of `gbar … k` over `ζ ≤ 0` (definitional). -/
theorem fbar_succ {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (k : ℕ) (v : Fin L → ℝ) :
    fbar c hh p γ μ (k + 1) v = ⨅ ζ : Set.Iic (0 : ℝ), gbar c hh p γ μ k v ζ := rfl

/-- `fbar … 0 = 0`, condition (2) (definitional). -/
theorem fbar_zero {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (v : Fin L → ℝ) :
    fbar c hh p γ μ 0 v = 0 := rfl

end ZipkinLostSales.LNatural
