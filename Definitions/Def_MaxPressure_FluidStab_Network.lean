import Mathlib

namespace MaxPressure.FluidStab

open Matrix

/-!
Dai and Lin (2005), *Maximum pressure policies in stochastic processing networks*, §§2–5
(pp. 199–203): the network data, the input-output matrix (5), the allocation set 𝒜 of (1)–(2),
its extreme points ℰ, the network pressure (6), the EAA Assumption (Assumption 1), the static
planning LP (9)–(13), Assumption 2, the fluid model (14)–(18), regular points, the maximum
pressure fluid model equation (20) and fluid model stability (Definition 4).

Index conventions. Internal buffers `1, …, I` are `Fin I`; buffers `0, …, I` (with the outside,
Buffer 0) are `Fin (I + 1)`, Buffer 0 being `0` and internal buffer `i : Fin I` being `i.succ`.
Activities `1, …, J` are `Fin J` and processors `1, …, K` are `Fin K` (0-based: the paper's label
`n` is the index `n - 1`). Time is real; paths are only evaluated at `t ≥ 0`, and every condition
quantifies over `t ≥ 0` (or `0 ≤ s ≤ t`).
-/

/-- The data of a stochastic processing network (§2.1–§2.3, §2.5, pp. 199–200):
* `A k j = 1` iff activity `j` requires processor `k` (the resource consumption matrix);
* `B j i = 1` iff activity `j` processes buffer `i` (column `0` is Buffer 0);
* `inputProc k` says that processor `k` is an input processor (the others are service
  processors);
* `m j` is the mean processing requirement of activity `j`, (3);
* `P j` is the routing matrix `P^j` of activity `j`, (4), indexed by buffers `0, …, I`. -/
structure Network (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin J) (Fin (I + 1)) ℝ
  inputProc : Fin K → Prop
  m : Fin J → ℝ
  P : Fin J → Matrix (Fin (I + 1)) (Fin (I + 1)) ℝ

variable {I J K : ℕ}

/-- Activity `j` is an **input activity** (p. 199): its constituency is `ℬ_j = {0}`. -/
def IsInputActivity (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 1 ∧ ∀ i : Fin I, N.B j i.succ = 0

/-- Activity `j` is a **service activity** (p. 199): `0 ∉ ℬ_j`. -/
def IsServiceActivity (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 0

/-- The standing assumptions of §2 (pp. 199–200), plus two disclosed ones:
1. `A` and `B` are 0–1 matrices;
2. every constituency is nonempty (p. 199);
3. every activity is an input activity or a service activity (p. 199);
4. every activity needs at least one processor (p. 199);
5. a processor processes input activities only (input processor) or service activities only
   (service processor) (p. 199);
6. there is at least one input activity (p. 200);
7. (disclosed) every input processor has at least one activity — presupposed by "the input
   processors are never idle", (2); without it `𝒜 = ∅`;
8. (disclosed) `m_j > 0` — the page sets `μ_j = 1/m_j`;
9. the routing matrices are nonnegative with `P^j_{00} = 0` (from `Φ^j_{00}(ℓ) = 0` and (4)). -/
def Network.Standing (N : Network I J K) : Prop :=
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
  (∀ j, N.P j 0 0 = 0)

/-- The processing rate `μ_j = 1/m_j` (p. 200). -/
noncomputable def μ (N : Network I J K) (j : Fin J) : ℝ := 1 / N.m j

/-- The input-output matrix (5), p. 201:
`R_ij = μ_j (B_ji − ∑_{i' ∈ ℐ ∪ {0}} B_ji' P^j_{i'i})` for internal buffers `i` and activities `j`. -/
noncomputable def R (N : Network I J K) : Matrix (Fin I) (Fin J) ℝ :=
  fun i j => μ N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ)

/-- The allocation set `𝒜` (p. 200): the allocations `a ∈ ℝ^J_+` satisfying (1)
`∑_j A_kj a_j ≤ 1` for each processor `k` and (2) `∑_j A_kj a_j = 1` for each input
processor `k`. -/
def allocSet (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ (∀ k, ∑ j, N.A k j * a j ≤ 1) ∧
    (∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1)}

/-- The set `ℰ` of extreme allocations: the extreme points of `𝒜` (p. 200). -/
def extremeAllocs (N : Network I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (allocSet N)

/-- The total network pressure (6), p. 201: `p(a, z) = z · Ra`. -/
noncomputable def pressure (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) : ℝ :=
  z ⬝ᵥ (R N *ᵥ a)

/-- The constituent buffers of an allocation `a` (p. 202): the internal buffers `i` with
`∑_j a_j B_ji > 0`. -/
def constituentBuffers (N : Network I J K) (a : Fin J → ℝ) : Set (Fin I) :=
  {i | 0 < ∑ j, a j * N.B j i.succ}

/-- **Assumption 1 (EAA Assumption)**, p. 202: for every buffer-level vector `z ∈ ℝ^I_+` there is
an extreme allocation `a* ∈ ℰ` maximizing the network pressure over `ℰ`,
`p(a*, z) = max_{a ∈ ℰ} p(a, z)`, such that `z_i > 0` for every constituent buffer `i` of `a*`. -/
def EAA (N : Network I J K) : Prop :=
  ∀ z : Fin I → ℝ, (∀ i, 0 ≤ z i) →
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i

/-- `(x, ρ)` is a feasible solution of the static planning LP (9)–(13), p. 202:
(10) `Rx = 0`; (11) `∑_j A_kj x_j ≤ ρ` for each service processor `k`;
(12) `∑_j A_kj x_j = 1` for each input processor `k`; (13) `x ≥ 0`. -/
def LPFeasible (N : Network I J K) (x : Fin J → ℝ) (ρ : ℝ) : Prop :=
  R N *ᵥ x = 0 ∧
  (∀ k, ¬ N.inputProc k → ∑ j, N.A k j * x j ≤ ρ) ∧
  (∀ k, N.inputProc k → ∑ j, N.A k j * x j = 1) ∧
  ∀ j, 0 ≤ x j

/-- **Assumption 2**, p. 203: there is an `x ≥ 0` with `Rx > 0` (componentwise, every internal
buffer). -/
def Assumption2 (N : Network I J K) : Prop :=
  ∃ x : Fin J → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i, 0 < (R N *ᵥ x) i

/-- `(Z̄, T̄)` is a **fluid model solution** (14)–(18), p. 202:
(14) `Z̄_i(t) = Z̄_i(0) + ∑_{i' ∈ ℐ∪{0}} ∑_j T̄_j(t) μ_j B_ji' P^j_{i'i} − ∑_j T̄_j(t) μ_j B_ji`
for `t ≥ 0`; (15) `Z̄_i(t) ≥ 0` for `t ≥ 0`; (16) `∑_j A_kj (T̄_j(t) − T̄_j(s)) = t − s` for
`0 ≤ s ≤ t` and each input processor `k`; (17) the same with `≤` for every processor `k`;
(18) `T̄` is nondecreasing (on `[0, ∞)`) and `T̄(0) = 0`. -/
def IsFluidSolution (N : Network I J K) (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ i : Fin I,
    Zb t i = Zb 0 i
      + ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb t j * μ N j * N.B j i' * N.P j i' i.succ
      - ∑ j : Fin J, Tb t j * μ N j * N.B j i.succ) ∧
  (∀ t, 0 ≤ t → ∀ i, 0 ≤ Zb t i) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, N.inputProc k →
    ∑ j, N.A k j * (Tb t j - Tb s j) = t - s) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, ∑ j, N.A k j * (Tb t j - Tb s j) ≤ t - s) ∧
  MonotoneOn Tb (Set.Ici 0) ∧ Tb 0 = 0

/-- A time `t > 0` is a **regular point** of `(Z̄, T̄)` (p. 203) if the solution is
differentiable at `t`. -/
def IsRegular {n m : ℕ} (Zb : ℝ → Fin n → ℝ) (Tb : ℝ → Fin m → ℝ) (t : ℝ) : Prop :=
  0 < t ∧ DifferentiableAt ℝ Zb t ∧ DifferentiableAt ℝ Tb t

/-- The **maximum pressure fluid model equation** (20), p. 203: at each regular time `t`,
`R Ṫ(t) · Z̄(t) = max_{a ∈ ℰ} Ra · Z̄(t)`, i.e. `p(Ṫ(t), Z̄(t))` is the greatest element of
`{p(a, Z̄(t)) : a ∈ ℰ}` (attained, and dominating). -/
def MPFluidEq (N : Network I J K) (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  ∀ t, IsRegular Zb Tb t →
    IsGreatest ((fun a => pressure N a (Zb t)) '' extremeAllocs N)
      (pressure N (deriv Tb t) (Zb t))

/-- A fluid model, given as the predicate `FM` on pairs `(Z̄, T̄)` that singles out its
solutions, is **stable** (Definition 4, p. 203) if there is a constant `δ > 0` such that every
fluid model solution with `|Z̄(0)| ≤ 1` has `Z̄(t) = 0` for `t ≥ δ`. The norm `|·|` is the
Euclidean norm. -/
def FluidStable {n m : ℕ} (FM : (ℝ → Fin n → ℝ) → (ℝ → Fin m → ℝ) → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ Zb Tb, FM Zb Tb → Real.sqrt (∑ i, Zb 0 i ^ 2) ≤ 1 →
    ∀ t, δ ≤ t → Zb t = 0

end MaxPressure.FluidStab
