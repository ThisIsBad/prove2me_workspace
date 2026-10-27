import Mathlib

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory ContDiff

/-- The ambient space `ℝⁿ`, with its Euclidean structure (the paper's norm `|·|` is the separate
`ℓ¹` function `l1` below). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `X ⊆ ℝⁿ` is a polytope: the convex hull of a finite nonempty set of points (§2.1, p. 4). Its
dimension `m` is `Module.finrank ℝ (vectorSpan ℝ X)`, unrestricted. -/
def IsPolytope {n : ℕ} (X : Set (E n)) : Prop :=
  ∃ S : Finset (E n), S.Nonempty ∧ X = convexHull ℝ (S : Set (E n))

/-- The paper's norm `|v| = ∑ᵢ |vᵢ|`, the `ℓ¹` norm on `ℝⁿ` (p. 5). -/
def l1 {n : ℕ} (v : E n) : ℝ := ∑ i, |v i|

/-- The tangent cone `TX(x) = {t (y - x) : y ∈ X, t ≥ 0}` (p. 4). -/
def tanCone {n : ℕ} (X : Set (E n)) (x : E n) : Set (E n) :=
  {v | ∃ y ∈ X, ∃ t : ℝ, 0 ≤ t ∧ v = t • (y - x)}

/-- `B_r = {u ∈ TX : |u| ≤ r}`, where `TX = vectorSpan ℝ X` is the direction of the affine hull
of `X` (p. 5). -/
def ballR {n : ℕ} (X : Set (E n)) (r : ℝ) : Set (E n) :=
  {u | u ∈ vectorSpan ℝ X ∧ l1 u ≤ r}

open Classical in
/-- The running cost (3.1): `L(x, v) = ∑ᵢ Ψᵢ(x) [vᵢ]₊` if `v ∈ TX(x) ∩ B_r`, and `+∞` otherwise
(p. 7). -/
noncomputable def runCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x v : E n) : ℝ≥0∞ :=
  if v ∈ tanCone X x ∧ v ∈ ballR X r then ENNReal.ofReal (∑ i, Ψ x i * max (v i) 0) else ⊤

/-- `φ ∈ Φ_T`: `T ≥ 0` and `φ` restricted to `[0, T]` is a Lipschitz continuous path into `X`
(p. 4). Values of `φ` outside `[0, T]` play no role. -/
def IsPath {n : ℕ} (X : Set (E n)) (T : ℝ) (φ : ℝ → E n) : Prop :=
  0 ≤ T ∧ (∃ K : NNReal, LipschitzOnWith K φ (Set.Icc 0 T)) ∧ Set.MapsTo φ (Set.Icc 0 T) X

/-- The path cost (2.2) with running cost (3.1): `c(φ) = ∫₀ᵀ L(φ(t), φ̇(t)) dt` (p. 5), as a lower
integral in `[0, +∞]`; `φ̇` is the derivative of `φ` within `[0, T]` (it exists for almost every
`t`, `φ` being Lipschitz). -/
noncomputable def pathCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (T : ℝ)
    (φ : ℝ → E n) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc 0 T, runCost X Ψ r (φ t) (derivWithin φ (Set.Icc 0 T) t)

/-- `C(x₀, x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) = x₀, φ(T) = x}` (p. 12). -/
noncomputable def minCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x0 x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 = x0 ∧ φ T = x), pathCost X Ψ r T φ

/-- The value function of the source problem (SP) for `X₀`:
`V(x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) ∈ X₀, φ(T) = x}` (p. 5). -/
noncomputable def srcVal {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 ∈ X0 ∧ φ T = x), pathCost X Ψ r T φ

/-- The value function of the target problem (TP) for `Y`:
`W(x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) = x, φ(T) ∈ Y}` (p. 5). -/
noncomputable def tgtVal {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (Y : Set (E n))
    (x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 = x ∧ φ T ∈ Y), pathCost X Ψ r T φ

/-- The maximized Hamiltonian (3.4): `H(x, u) = max_{v ∈ TX ∩ B_r} (⟨u, v⟩ - ⟨Ψ(x), [v]₊⟩)`
(pp. 7–8). `B_r` is compact and contains `0`, so the supremum is attained. -/
noncomputable def ham {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x u : E n) : ℝ :=
  sSup ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r)

/-- `‖Ψ‖∞ = max_{x ∈ X} |Ψ(x)|`, with `|·|` the `ℓ¹` norm (p. 8). -/
noncomputable def psiNorm {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) : ℝ :=
  sSup ((fun x => l1 (Ψ x)) '' X)

/-- The `m`-dimensional Hausdorff measure, `m = dim X`, restricted to the relative interior `X°`:
the measure behind "for almost all `x ∈ X°`" in (3.9), (3.10). -/
noncomputable def interiorMeasure {n : ℕ} (X : Set (E n)) : MeasureTheory.Measure (E n) :=
  (μH[(Module.finrank ℝ (vectorSpan ℝ X) : ℝ)]).restrict (intrinsicInterior ℝ X)

/-- `DV(x) = w`: `w ∈ TX` and `V` has the derivative `z ↦ ⟨w, z⟩` at `x` relative to `X` (p. 4 and
p. 13, where `DV(x) ∈ L(TX, ℝ)` is identified with the unique such `w ∈ TX`). -/
def relGrad {n : ℕ} (X : Set (E n)) (V : E n → ℝ) (x w : E n) : Prop :=
  w ∈ vectorSpan ℝ X ∧ HasFDerivWithinAt V (innerSL ℝ w) X x

/-- First line of (3.9): `H(x, DV(x)) ≤ 0` for almost all `x ∈ X°` (p. 9). -/
def AESubsol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (V : E n → ℝ) : Prop :=
  ∀ᵐ x ∂(interiorMeasure X), ∃ w, relGrad X V x w ∧ ham X Ψ r x w ≤ 0

/-- First line of (3.10): `H(x, -DW(x)) ≤ 0` for almost all `x ∈ X°` (p. 9). -/
def AESubsolNeg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (W : E n → ℝ) : Prop :=
  ∀ᵐ x ∂(interiorMeasure X), ∃ w, relGrad X W x w ∧ ham X Ψ r x (-w) ≤ 0

/-- Definition 1 (p. 11), subsolution part: `V ∈ C(X)`, `V = 0` on `X₀`, and for every test
function `ϕ ∈ C^∞` such that `V - ϕ` has a (local, relative to `X`) maximum at
`x₀ ∈ X° ∖ X₀`, `H(x₀, Dϕ(x₀)) ≤ 0`. -/
def IsViscSub {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  ContinuousOn V X ∧ (∀ x ∈ X0, V x = 0) ∧
    ∀ ϕ : E n → ℝ, ContDiff ℝ ∞ ϕ → ∀ x0 ∈ intrinsicInterior ℝ X \ X0,
      IsLocalMaxOn (fun x => V x - ϕ x) X x0 → ham X Ψ r x0 (gradient ϕ x0) ≤ 0

/-- Definition 1 (p. 11), supersolution part: `V ∈ C(X)`, `V = 0` on `X₀`, and for every test
function `ϕ ∈ C^∞` such that `V - ϕ` has a (local, relative to `X`) minimum at `x₀ ∈ X ∖ X₀`,
`H(x₀, Dϕ(x₀)) ≥ 0`. -/
def IsViscSuper {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  ContinuousOn V X ∧ (∀ x ∈ X0, V x = 0) ∧
    ∀ ϕ : E n → ℝ, ContDiff ℝ ∞ ϕ → ∀ x0 ∈ X \ X0,
      IsLocalMinOn (fun x => V x - ϕ x) X x0 → 0 ≤ ham X Ψ r x0 (gradient ϕ x0)

/-- Definition 1 (p. 11): a viscosity solution of (4.1). -/
def IsViscSol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  IsViscSub X Ψ r X0 V ∧ IsViscSuper X Ψ r X0 V

/-- Definition 2 (p. 12): a maximal viscosity solution of (4.1). -/
def IsMaxViscSol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  IsViscSol X Ψ r X0 V ∧ ∀ V' : E n → ℝ, IsViscSol X Ψ r X0 V' → ∀ x ∈ X, V' x ≤ V x

end SemilinearHJ.Verification
