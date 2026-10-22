import Mathlib

open MeasureTheory Filter Topology

namespace MaxPressure.Throughput

/-! Dai and Lin (2005), §§2–5. Buffers 1,…,I are `Fin I`, with paper buffer 0
represented by 0 in `Fin (I+1)` and internal buffer i by `i.succ`. Activity
and processor labels are shifted from the paper's 1-based labels to `Fin`. -/

/-- Network primitives of §§2.1–2.3 and 2.5. -/
structure Network (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin J) (Fin (I + 1)) ℝ
  inputProc : Fin K → Prop
  m : Fin J → ℝ
  P : Fin J → Matrix (Fin (I + 1)) (Fin (I + 1)) ℝ

def IsInputActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 1 ∧ ∀ i : Fin I, N.B j i.succ = 0

def IsServiceActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 0

/-- Standing conventions of §2. Positivity of `m` and activity coverage of input
processors are disclosed necessary refinements of the paper's wording. The row
conditions on `P` follow from the routing-count conditions and (4). -/
def Network.Standing {I J K : ℕ} (N : Network I J K) : Prop :=
  (∀ k j, N.A k j = 0 ∨ N.A k j = 1) ∧
  (∀ j i, N.B j i = 0 ∨ N.B j i = 1) ∧
  (∀ j, ∃ i, N.B j i = 1) ∧
  (∀ j, IsInputActivity N j ∨ IsServiceActivity N j) ∧
  (∀ j, ∃ k, N.A k j = 1) ∧
  (∀ k j, N.A k j = 1 → (N.inputProc k ↔ IsInputActivity N j)) ∧
  (∃ j, IsInputActivity N j) ∧
  (∀ k, N.inputProc k → ∃ j, N.A k j = 1) ∧
  (∀ j, 0 < N.m j) ∧
  (∀ j i i', 0 ≤ N.P j i i') ∧
  (∀ j, N.P j 0 0 = 0) ∧
  (∀ j i, N.B j i = 1 → ∑ i', N.P j i i' = 1) ∧
  (∀ j i i', N.B j i = 0 → N.P j i i' = 0)

/-- Processing rate μ_j = 1/m_j. -/
noncomputable def mu {I J K : ℕ} (N : Network I J K) (j : Fin J) : ℝ :=
  1 / N.m j

/-- Input-output matrix R of (5), with its row sum including buffer 0. -/
noncomputable def R {I J K : ℕ} (N : Network I J K) :
    Matrix (Fin I) (Fin J) ℝ :=
  fun i j => mu N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ)

/-- Allocations satisfying (1) and (2). -/
def allocSet {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧
    (∀ k, ∑ j, N.A k j * a j ≤ 1) ∧
    (∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1)}

/-- Extreme allocations of the allocation polytope. -/
def extremeAllocs {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (allocSet N)

/-- Network pressure p(a,z) of (6). -/
noncomputable def pressure {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (z : Fin I → ℝ) : ℝ :=
  dotProduct z (Matrix.mulVec (R N) a)

/-- Internal buffers that can generate positive flow under allocation a. -/
def constituentBuffers {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) : Set (Fin I) :=
  {i | 0 < ∑ j, a j * N.B j i.succ}

/-- Assumption 1: a pressure maximizer can be chosen with positive levels at
all its constituent buffers. The comparison formulation includes attainment. -/
def EAA {I J K : ℕ} (N : Network I J K) : Prop :=
  ∀ z : Fin I → ℝ, (∀ i, 0 ≤ z i) →
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i

/-- Feasibility of the static planning LP (10)–(13). -/
def LPFeasible {I J K : ℕ} (N : Network I J K)
    (x : Fin J → ℝ) (rho : ℝ) : Prop :=
  Matrix.mulVec (R N) x = 0 ∧
  (∀ k, ¬ N.inputProc k → ∑ j, N.A k j * x j ≤ rho) ∧
  (∀ k, N.inputProc k → ∑ j, N.A k j * x j = 1) ∧
  ∀ j, 0 ≤ x j

/-- Fluid model equations (14)–(18), for time t ≥ 0. -/
def IsFluidSolution {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ i,
    Zb t i = Zb 0 i +
      ∑ i' : Fin (I + 1), ∑ j : Fin J,
        Tb t j * mu N j * N.B j i' * N.P j i' i.succ -
      ∑ j : Fin J, Tb t j * mu N j * N.B j i.succ) ∧
  (∀ t, 0 ≤ t → ∀ i, 0 ≤ Zb t i) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, N.inputProc k →
    ∑ j, N.A k j * (Tb t j - Tb s j) = t - s) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k,
    ∑ j, N.A k j * (Tb t j - Tb s j) ≤ t - s) ∧
  MonotoneOn Tb (Set.Ici (0 : ℝ)) ∧ Tb 0 = 0

/-- A positive time at which both fluid paths are differentiable. -/
def IsRegular {I J : ℕ} (Zb : ℝ → Fin I → ℝ)
    (Tb : ℝ → Fin J → ℝ) (t : ℝ) : Prop :=
  0 < t ∧ DifferentiableAt ℝ Zb t ∧ DifferentiableAt ℝ Tb t

/-- Maximum-pressure fluid equation (20). `IsGreatest` records attainment. -/
noncomputable def MPFluidEq {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  ∀ t, IsRegular Zb Tb t →
    IsGreatest ((fun a => pressure N a (Zb t)) '' extremeAllocs N)
      (pressure N (deriv Tb t) (Zb t))

/-- Definition 3, weak stability of a fluid model. -/
def WeaklyStable {I J : ℕ}
    (FM : (ℝ → Fin I → ℝ) → (ℝ → Fin J → ℝ) → Prop) : Prop :=
  ∀ Zb Tb, FM Zb Tb → Zb 0 = 0 → ∀ t, 0 ≤ t → Zb t = 0

end MaxPressure.Throughput
