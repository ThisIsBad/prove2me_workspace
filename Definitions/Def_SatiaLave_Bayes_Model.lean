import Mathlib

open MeasureTheory

namespace SatiaLave.Bayes

/-- The parameter space of the unknown transition-probability matrix `P`
(Satia–Lave 1973, p. 733): `P i k` is the row `p_i^k`, i.e. `P i k j = p^k_{ij}`.
It carries the product (Borel) σ-algebra. -/
abbrev Mat (S : Type*) (D : S → Type*) : Type _ := (i : S) → D i → S → ℝ

/-- A finite discounted Markovian decision process whose transition-probability rows are only
known to lie in closed convex sets (Satia–Lave 1973, pp. 728–729 and Eq. (1)).
`S` is the finite set of states, `D i` the finite set of decisions available in state `i`,
`r i k j = r^k_{ij}` the reward of a transition `i → j` under decision `k`, `β` the discount
factor, and `U i k = S_i^k` the set of admissible rows `p_i^k`. -/
structure UncertainMDP (S : Type*) (D : S → Type*) [Fintype S] where
  /-- rewards `r^k_{ij}` -/
  r : (i : S) → D i → S → ℝ
  /-- discount factor `β` -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the uncertainty sets `S_i^k` of admissible probability rows -/
  U : (i : S) → D i → Set (S → ℝ)
  U_subset : ∀ i k, U i k ⊆ stdSimplex ℝ S
  U_closed : ∀ i k, IsClosed (U i k)
  U_convex : ∀ i k, Convex ℝ (U i k)
  U_nonempty : ∀ i k, (U i k).Nonempty

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]

/-- `P` is a transition-probability matrix: every row `p_i^k` is a probability vector. -/
def IsStoch (P : Mat S D) : Prop := ∀ i k, P i k ∈ stdSimplex ℝ S

/-- A prior on the unknown matrix: a probability measure concentrated on the
transition-probability matrices. (The paper writes a density `g(P)`; every density defines
such a measure, and the paper's own proof of Proposition 9 uses point masses.) -/
def IsPrior (g : Measure (Mat S D)) : Prop :=
  IsProbabilityMeasure g ∧ g {P : Mat S D | IsStoch P}ᶜ = 0

/-- The prior mean `p̄^k_{ij} = E(p^k_{ij})` (p. 733). -/
noncomputable def pbar (g : Measure (Mat S D)) (i : S) (k : D i) (j : S) : ℝ :=
  ∫ P, P i k j ∂g

/-- The Bayes transformation `T^m_{lj} g` of Eq. (8): the posterior after observing a
transition `l → j` under decision `m`, `T^m_{lj} g(P) = C p^m_{lj} g(P)` with `C = 1 / p̄^m_{lj}`.
When `p̄^m_{lj} = 0` no normalizing constant exists; the convention returns `g` itself (this
posterior is always multiplied by `p̄^m_{lj} = 0` in Eq. (10)). -/
noncomputable def bayes (g : Measure (Mat S D)) (l : S) (m : D l) (j : S) : Measure (Mat S D) :=
  if pbar g l m j = 0 then g
  else (ENNReal.ofReal (pbar g l m j))⁻¹ • g.withDensity (fun P => ENNReal.ofReal (P l m j))

/-- `f` solves the recursive equations (10) (equivalently (9)) at every prior:
`f(i, g) = max_k { Σ_j p̄^k_{ij} r^k_{ij} + β Σ_j p̄^k_{ij} f(j, T^k_{ij} g) }`. -/
def SolvesEq10 (M : UncertainMDP S D) (f : S → Measure (Mat S D) → ℝ) : Prop :=
  ∀ i g, IsPrior g → f i g = Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ∑ j, pbar g i k j * M.r i k j + M.β * ∑ j, pbar g i k j * f j (bayes g i k j))

/-- `f` is bounded on the set of (state, prior) pairs. -/
def IsBoundedOnPriors (f : S → Measure (Mat S D) → ℝ) : Prop :=
  ∃ C : ℝ, ∀ i g, IsPrior g → |f i g| ≤ C

/-- `V` solves the optimality equations of the Markovian decision process with the known
transition matrix `P`: `V_i = max_k Σ_j p^k_{ij} (r^k_{ij} + β V_j)`. -/
def SolvesKnown (M : UncertainMDP S D) (P : Mat S D) (V : S → ℝ) : Prop :=
  ∀ i, V i = Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ∑ j, P i k j * (M.r i k j + M.β * V j))

/-- `V` solves the max-max equations (p. 735):
`V_i^+ = max_{k ∈ K_i} max_{P ∈ S} { Σ_j p^k_{ij} r^k_{ij} + β Σ_j p^k_{ij} V_j^+ }`;
only the row `p_i^k ∈ S_i^k` enters, so the inner max ranges over `S_i^k`. -/
def SolvesVplus (M : UncertainMDP S D) (V : S → ℝ) : Prop :=
  ∀ i, V i = Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ⨆ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j))

/-- `V` solves the max-min equations (p. 736):
`V_i^- = max_k min_{P ∈ S} { Σ_j p^k_{ij} r^k_{ij} + β Σ_j p^k_{ij} V_j^- }`. -/
def SolvesVminus (M : UncertainMDP S D) (V : S → ℝ) : Prop :=
  ∀ i, V i = Finset.univ.sup' Finset.univ_nonempty (fun k : D i =>
    ⨅ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * V j))

/-- The set `S = {P : p_i^k ∈ S_i^k for all i and all k}` of matrices consistent with the
uncertainty sets (p. 729). -/
def consistentSet (M : UncertainMDP S D) : Set (Mat S D) :=
  {P | ∀ i k, P i k ∈ M.U i k}

/-- `α = prob(P ∈ S | g)` (p. 735). -/
noncomputable def alpha (M : UncertainMDP S D) (g : Measure (Mat S D)) : ℝ :=
  (g (consistentSet M)).toReal

omit [DecidableEq S] [∀ i, DecidableEq (D i)] in
/-- The triples `(i, k, j)` form a nonempty finite type. -/
theorem triples_nonempty :
    (Finset.univ : Finset ((Σ i, D i) × S)).Nonempty :=
  ⟨(⟨Classical.arbitrary S, Classical.arbitrary _⟩, Classical.arbitrary S), Finset.mem_univ _⟩

/-- `max_{i,j,k} [r^k_{ij} / (1 - β)]` (p. 735). -/
noncomputable def rmax (M : UncertainMDP S D) : ℝ :=
  Finset.univ.sup' (triples_nonempty (S := S) (D := D))
    (fun x : (Σ i, D i) × S => M.r x.1.1 x.1.2 x.2 / (1 - M.β))

/-- `min_{i,j,k} [r^k_{ij} / (1 - β)]` (p. 736). -/
noncomputable def rmin (M : UncertainMDP S D) : ℝ :=
  Finset.univ.inf' (triples_nonempty (S := S) (D := D))
    (fun x : (Σ i, D i) × S => M.r x.1.1 x.1.2 x.2 / (1 - M.β))

/-- The `N × N` transition matrix `P^A` of the pure stationary policy `A` under `P`. -/
def policyMatrix (P : Mat S D) (A : (i : S) → D i) : Matrix S S ℝ :=
  fun i j => P i (A i) j

/-- The expected one-step reward vector `[q]_i = Σ_j p^A_{ij} r^A_{ij}`. -/
def policyReward (M : UncertainMDP S D) (P : Mat S D) (A : (i : S) → D i) : S → ℝ :=
  fun i => ∑ j, P i (A i) j * M.r i (A i) j

/-- The total expected discounted return of the pure stationary policy `A` when the
transition matrix is `P` (proof of Proposition 10, p. 736):
`[q + β P^A q + β² [P^A]² q + ⋯]_i`. -/
noncomputable def policyValue (M : UncertainMDP S D) (A : (i : S) → D i) (P : Mat S D) (i : S) :
    ℝ :=
  ∑' n : ℕ, M.β ^ n * (((policyMatrix P A) ^ n).mulVec (policyReward M P A)) i

end SatiaLave.Bayes
