import Mathlib

namespace CoffmanMitrani1980.Region

open Finset

/-- The data of the queueing model of Coffman and Mitrani, *A Characterization of Waiting Time
Performance Realizable by Single-Server Queues*, Operations Research 28 (1980), §1, p. 811 (PDF 3)
and p. 812–813 (PDF 4–5): a single server, `M` job classes, class `i` arriving in a Poisson stream
at rate `lam i` with exponential service times of parameter `mu i`, together with the standing
assumptions of the paper: every rate is positive ("at rate λᵢ", "with parameter μᵢ"), and the total
traffic intensity `ρ = Σ λᵢ/μᵢ` is below `1`, "the condition for the existence of a stationary
distribution" (p. 812), the only systems the paper considers.

**Formalization Note.** Classes are indexed by `Fin M`, numbered from `0`: the paper's class `i`
is `i - 1` here. Only the numerical parameters enter the statements of this mission; the stochastic
model itself is not formalized. -/
structure Params (M : ℕ) where
  /-- arrival rate `λᵢ` of class `i` -/
  lam : Fin M → ℝ
  /-- service rate `μᵢ` of class `i` (mean service time `1/μᵢ`) -/
  mu : Fin M → ℝ
  lam_pos : ∀ i, 0 < lam i
  mu_pos : ∀ i, 0 < mu i
  /-- stability: `ρ = Σᵢ λᵢ/μᵢ < 1` (p. 812) -/
  load_lt_one : ∑ i, lam i / mu i < 1

/-- Traffic intensity of class `i`, `ρᵢ = λᵢ/μᵢ` (p. 811). -/
noncomputable def Params.rho {M : ℕ} (p : Params M) (i : Fin M) : ℝ := p.lam i / p.mu i

/-- The coefficient `aᵢ = ρᵢ/μᵢ` of the proof of Lemma 2 (p. 818). -/
noncomputable def Params.a {M : ℕ} (p : Params M) (i : Fin M) : ℝ := p.rho i / p.mu i

/-- The constant `V = Σᵢ λᵢ/μᵢ²` of the conservation law (1) (p. 813). -/
noncomputable def Params.V {M : ℕ} (p : Params M) : ℝ := ∑ i, p.lam i / p.mu i ^ 2

/-- The right-hand side of the inequalities (4) (pp. 816–817), as a function of the set of classes
`g`: `f(g) = (Σ_{i∈g} ρᵢ/μᵢ) / (1 - Σ_{i∈g} ρᵢ)`. The denominator is positive for every `g`
because `Σ_{i∈g} ρᵢ ≤ ρ < 1`. `f(∅) = 0`, the paper's convention "If g₁₂ is empty, we shall define
all sums involved in (4) as zero" (p. 818). -/
noncomputable def Params.f {M : ℕ} (p : Params M) (g : Finset (Fin M)) : ℝ :=
  (∑ i ∈ g, p.a i) / (1 - ∑ i ∈ g, p.rho i)

/-- **H\*\*** (Lemma 2, p. 817, PDF 9): the set of performance vectors `W = (W₁, …, W_M)` which
satisfy the conservation law (1), `Σᵢ ρᵢ Wᵢ = V/(1 - ρ)` (p. 813), and the `2^M - 2` inequalities
(4), `Σ_{i∈g} ρᵢ Wᵢ ≥ f(g)` for every proper nonempty subset `g` of the classes.

**Formalization Note.** (1) is stated literally with `V` and `ρ = Σᵢ ρᵢ`; that it is the case
`g = univ` of (4) with equality is a fact, not part of the definition. This set replaces the paper's
H\* ("achievable by some scheduling strategy"), which rests on a strategy class described only in
prose. -/
def Params.Hss {M : ℕ} (p : Params M) : Set (Fin M → ℝ) :=
  {W | ∑ i, p.rho i * W i = p.V / (1 - ∑ i, p.rho i) ∧
    ∀ g : Finset (Fin M), g.Nonempty → g ≠ univ → p.f g ≤ ∑ i ∈ g, p.rho i * W i}

/-- The `k` highest-priority classes of the priority order `π`: `{π 0, …, π (k-1)}`.

**Formalization Note.** A priority order is a permutation `π : Equiv.Perm (Fin M)` with `π r` the
class of rank `r`, rank `0` being the highest priority; the paper's `P(i₁, i₂, …, i_M)` (class `i₁`
first) has `π 0 = i₁ - 1`, `π 1 = i₂ - 1`, …. -/
def topSet {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) : Finset (Fin M) :=
  (univ.filter fun j : Fin M => (j : ℕ) < k).image π

/-- The **preemptive priority vector** `P(i₁, …, i_M)` (p. 815, PDF 7), the performance vector of the
discipline giving preemptive priority to class `i₁`, then `i₂`, and so on. With `S_k = {i₁, …, i_k}`
and `S₀ = ∅`, its component for the class of rank `k` is
`P_{i_k} = (f(S_k) - f(S_{k-1})) / ρ_{i_k}`, the unique solution of the equations (5) for the chain
`S₁ ⊂ S₂ ⊂ ⋯ ⊂ S_M` (end of the proof of Lemma 2, p. 818, PDF 10).

**Formalization Note.** The paper names these vectors and never computes them; the closed form here is
the solution of (5) for the chain of top sets, the identification the proof of Lemma 2 makes. For
the class `i` of rank `r = π⁻¹ i`, `S_{r+1} = topSet π (r+1)` and `S_r = topSet π r`. The division
is by `ρᵢ > 0`. -/
noncomputable def Params.prioVec {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M)) : Fin M → ℝ :=
  fun i => (p.f (topSet π ((π.symm i : ℕ) + 1)) - p.f (topSet π (π.symm i : ℕ))) / p.rho i

/-- **H**, (3) (p. 815, PDF 7): `W ∈ H` iff there exist `M` points `P₁, …, P_M` from the set of the
`M!` preemptive priority vectors and numbers `α₁, …, α_M ≥ 0` with `α₁ + ⋯ + α_M = 1` and
`W = Σᵢ αᵢ Pᵢ`.

**Formalization Note.** The `M` points are `prioVec (σ k)`, `k : Fin M`, for an arbitrary map
`σ : Fin M → Equiv.Perm (Fin M)`, so repetitions are allowed, as (3) allows. The paper's "α_m" is a
misprint for `α_M`. -/
def Params.H {M : ℕ} (p : Params M) : Set (Fin M → ℝ) :=
  {W | ∃ (σ : Fin M → Equiv.Perm (Fin M)) (α : Fin M → ℝ),
    (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧ W = ∑ k, α k • p.prioVec (σ k)}

end CoffmanMitrani1980.Region
