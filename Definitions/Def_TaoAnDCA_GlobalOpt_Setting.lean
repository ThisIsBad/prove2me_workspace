import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open Filter Topology

namespace TaoAnDCA.GlobalOpt

/-- `dom θ = {x ∈ X : θ(x) < +∞}` (p. 481). -/
def effDom {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | θ x ≠ ⊤}

/-- The d.c. difference `(g − h)(x)` under the paper's convention `+∞ − (+∞) = +∞` (p. 481). -/
noncomputable def dcSub {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  if g x = ⊤ then ⊤ else g x - h x

/-- The exact subdifferential `∂θ(x)` as a set (p. 481), through the published predicate. -/
def subdiff {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | InertialFB.IFB.IsSubgradient θ x y}

/-- The `ε`-subdifferential `∂_ε θ(x₀)` (p. 481), defined for `x₀ ∈ dom θ`. -/
def epsSubdiff {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (ε : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | θ x₀ ≠ ⊤ ∧ ∀ x, θ x₀ + ((inner ℝ (x - x₀) y - ε : ℝ) : EReal) ≤ θ x}

/-- Standing assumptions: `g, h ∈ Γ₀(X)` (p. 481) and the inclusions (3) (p. 482). -/
structure DCStanding {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Prop where
  g_mem : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g
  h_mem : ThreeOpSplitting.ConvexRates.IsProperClosedConvex h
  dom_g_sub : effDom g ⊆ effDom h
  dom_conj_h_sub : effDom (CondatPD.FinDim.conj h) ⊆ effDom (CondatPD.FinDim.conj g)

/-- `α = inf {g(x) − h(x) : x ∈ X}`, problem (P) (p. 481). -/
noncomputable def primalValue {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : EReal :=
  ⨅ x, dcSub g h x

/-- The solution set `𝒫` of (P). -/
def primalSol {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ z, dcSub g h x ≤ dcSub g h z}

/-- The solution set `𝒟` of (D) `inf {h*(y) − g*(y) : y ∈ Y}` (p. 482). -/
def dualSol {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ z, dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y ≤
    dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) z}

end TaoAnDCA.GlobalOpt
