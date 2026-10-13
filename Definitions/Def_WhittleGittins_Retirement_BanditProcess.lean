import Mathlib

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Whittle's multi-project bandit process (Sections 1–2, pp. 143–144): `N` projects indexed by
`Fin N`; project `i` has a measurable state space `X i`, a Markov transition kernel `P i` (which
may depend on `i`), and a measurable expected one-step reward `R i`. Rewards are discounted by
`β` with `0 ≤ β < 1` and satisfy the uniform bound (1), `k(1 − β) ≤ Rᵢ(xᵢ) ≤ K(1 − β)`. -/
structure BanditProcess (N : ℕ) (X : Fin N → Type*) [∀ i, MeasurableSpace (X i)] where
  /-- Transition kernel of project `i` (applied only when project `i` is engaged). -/
  P : ∀ i, Kernel (X i) (X i)
  P_markov : ∀ i, IsMarkovKernel (P i)
  /-- Expected immediate reward `Rᵢ(xᵢ)` of engaging project `i` in state `xᵢ`. -/
  R : ∀ i, X i → ℝ
  R_meas : ∀ i, Measurable (R i)
  /-- Discount factor. -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- The constants `k`, `K` of bound (1) (possibly negative). -/
  k : ℝ
  K : ℝ
  /-- Bound (1). -/
  bound : ∀ i (x : X i), k * (1 - β) ≤ R i x ∧ R i x ≤ K * (1 - β)

variable {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]

/-! ### Infinite horizon: the operators (3) and the value equations (2), (4), (9) -/

/-- The operator `Lᵢ` of (3): `Lᵢ θ(x) = Rᵢ(xᵢ) + β E[θ(x(t+1)) | x(t) = x, i(t) = i]`, where only
the `i`th component of the state moves, according to `P i`. -/
noncomputable def Lop (B : BanditProcess N X) (i : Fin N) (θ : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    ℝ :=
  B.R i (x i) + B.β * ∫ y, θ (Function.update x i y) ∂(B.P i (x i))

/-- The one-project version of `Lᵢ`, acting on functions of `xᵢ` only. -/
noncomputable def Lop1 (B : BanditProcess N X) (i : Fin N) (ψ : X i → ℝ) (xi : X i) : ℝ :=
  B.R i xi + B.β * ∫ y, ψ y ∂(B.P i xi)

/-- `Φ` is the value of the continuing process: a bounded measurable solution of the dynamic
programming equation (2), `Φ = maxᵢ Lᵢ Φ`. (Bounded solutions of (2) are unique.) -/
def IsContinuingValue [NeZero N] (B : BanditProcess N X) (Φ : (∀ j, X j) → ℝ) : Prop :=
  Measurable Φ ∧ (∃ C : ℝ, ∀ x, |Φ x| ≤ C) ∧
    ∀ x, Φ x = Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i Φ x)

/-- `F` is the value of the `M`-process: for every retirement reward `M`, `F(·, M)` is a bounded
measurable solution of (4), `F = max(M, maxᵢ Lᵢ F)`. -/
def IsMProcessValue [NeZero N] (B : BanditProcess N X) (F : (∀ j, X j) → ℝ → ℝ) : Prop :=
  ∀ M : ℝ, Measurable (fun x => F x M) ∧ (∃ C : ℝ, ∀ x, |F x M| ≤ C) ∧
    ∀ x, F x M = max M (Finset.univ.sup' Finset.univ_nonempty (fun i => Lop B i (fun z => F z M) x))

/-- `φᵢ` is the value of the single-project `M`-process for project `i`: for every `M`,
`φᵢ(·, M)` is a bounded measurable solution of (9), `φᵢ = max(M, Lᵢ φᵢ)`. -/
def IsOneProjectValue (B : BanditProcess N X) (i : Fin N) (φ : X i → ℝ → ℝ) : Prop :=
  ∀ M : ℝ, Measurable (fun xi => φ xi M) ∧ (∃ C : ℝ, ∀ xi, |φ xi M| ≤ C) ∧
    ∀ xi, φ xi M = max M (Lop1 B i (fun z => φ z M) xi)

/-- The infinite-horizon index `Mᵢ(xᵢ)`: the infimal `M` with `φᵢ(xᵢ, M) = M`. -/
noncomputable def indexInf {i : Fin N} (φ : X i → ℝ → ℝ) (xi : X i) : ℝ :=
  sInf {M : ℝ | φ xi M = M}

/-! ### Finite horizons (Section 4): budgets `s`, the values `φᵢ(xᵢ, sᵢ, M)` and `F(x, s, M)` -/

/-- The projects that may still be engaged: those with remaining process time `sᵢ > 0`. -/
def active (s : Fin N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < s i)

/-- `Dᵢ s`: decrease `sᵢ` by one (applied only to active `i`). -/
def decr (s : Fin N → ℕ) (i : Fin N) : Fin N → ℕ :=
  Function.update s i (s i - 1)

/-- The right-hand side `max(M, maxᵢ gᵢ)` of a dynamic programming equation, the inner maximum
ranging over the active projects; equal to `M` when no project is active. -/
noncomputable def bellmanMax (s : Fin N → ℕ) (M : ℝ) (g : Fin N → ℝ) : ℝ :=
  if h : (active s).Nonempty then max M ((active s).sup' h g) else M

/-- `φᵢ(xᵢ, sᵢ, M)`: the single-project `M`-process value when project `i` may be operated at most
`sᵢ` more times, by the recursion (14): `φᵢ(xᵢ, 0, M) = M` and
`φᵢ(xᵢ, n + 1, M) = max(M, Rᵢ(xᵢ) + β E[φᵢ(xᵢ(t+1), n, M)])`. -/
noncomputable def phi (B : BanditProcess N X) (i : Fin N) : X i → ℕ → ℝ → ℝ
  | _, 0, M => M
  | xi, n + 1, M => max M (B.R i xi + B.β * ∫ y, phi B i y n M ∂(B.P i xi))

/-- Backward induction for the multi-project `M`-process, with an explicit fuel argument (the
intended fuel is `∑ i, sᵢ`, which every engagement decreases by one). -/
noncomputable def Fuel (B : BanditProcess N X) : ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      bellmanMax s M (fun i =>
        B.R i (x i) + B.β * ∫ y, Fuel B n (Function.update x i y) (decr s i) M ∂(B.P i (x i)))

/-- `F(x, s, M)`: the maximal expected reward of the `M`-process when the process time of project
`i` may not exceed `sᵢ`, i.e. the backward-induction value of `F = max(M, maxᵢ Lᵢ F)` (with `Lᵢ` as
in (15), maximum over active projects) and `F(x, 0, M) = M`. -/
noncomputable def F (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  Fuel B (∑ i, s i) x s M

/-- The finite-horizon index `Mᵢ(xᵢ, sᵢ)`: the infimal `M` with `φᵢ(xᵢ, sᵢ, M) = M`. It is only
meaningful for `sᵢ > 0`; for `sᵢ = 0` the paper's value is `−∞` and every use is guarded by
`0 < sᵢ`. -/
noncomputable def index (B : BanditProcess N X) (i : Fin N) (xi : X i) (n : ℕ) : ℝ :=
  sInf {M : ℝ | phi B i xi n M = M}

/-- Right derivative `∂f/∂m` at `m` (derivative within `[m, ∞)`). -/
noncomputable def rderiv (f : ℝ → ℝ) (m : ℝ) : ℝ :=
  derivWithin f (Set.Ici m) m

/-- `F̂(x, s, M) = K − ∫_M^K ∏ᵢ ∂φᵢ(xᵢ, sᵢ, m)/∂m dm`, formula (13). -/
noncomputable def Fhat (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  B.K - ∫ m in M..B.K, ∏ i, rderiv (fun m' => phi B i (x i) (s i) m') m

/-- `Pᵢ(x, s, M) = ∏_{j ≠ i} ∂φⱼ(xⱼ, sⱼ, M)/∂M`, formula (17). -/
noncomputable def Pdist (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N)
    (M : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, rderiv (fun m' => phi B j (x j) (s j) m') M

/-- `Lᵢ F̂(x, s, M)` with the extended operator (15):
`Rᵢ(xᵢ) + β E[F̂(x(t+1), Dᵢ s, M) | x(t) = x, i(t) = i]`. -/
noncomputable def LFhat (B : BanditProcess N X) (i : Fin N) (x : ∀ j, X j) (s : Fin N → ℕ)
    (M : ℝ) : ℝ :=
  B.R i (x i) + B.β * ∫ y, Fhat B (Function.update x i y) (decr s i) M ∂(B.P i (x i))

/-! ### Markov allocation policies with a retirement option -/

/-- A Markov allocation policy: in state `x` with budgets `s` and retirement reward `M` it engages
project `i` (`some i`) or retires (`none`). -/
abbrev Policy (N : ℕ) (X : Fin N → Type*) := (∀ j, X j) → (Fin N → ℕ) → ℝ → Option (Fin N)

/-- A policy is feasible if it only engages projects with remaining process time. -/
def IsFeasible (σ : Policy N X) : Prop :=
  ∀ x s M i, σ x s M = some i → 0 < s i

/-- A policy is measurable if each decision `{x | σ(x, s, M) = i}` is a measurable set of states. -/
def IsMeasurablePolicy (σ : Policy N X) : Prop :=
  ∀ s M i, MeasurableSet {x | σ x s M = some i}

/-- Expected discounted reward of a policy, with an explicit fuel argument (intended `∑ i, sᵢ`):
retiring yields `M`; engaging an active project `i` yields `Rᵢ(xᵢ)` plus `β` times the expected
value from the new state with budgets `Dᵢ s`. -/
noncomputable def polValueFuel (B : BanditProcess N X) (σ : Policy N X) :
    ℕ → (∀ j, X j) → (Fin N → ℕ) → ℝ → ℝ
  | 0, _, _, M => M
  | n + 1, x, s, M =>
      match σ x s M with
      | none => M
      | some i =>
          if 0 < s i then
            B.R i (x i) + B.β * ∫ y, polValueFuel B σ n (Function.update x i y) (decr s i) M
              ∂(B.P i (x i))
          else M

/-- The expected total discounted reward of the policy `σ` in the `M`-process from `(x, s)`. -/
noncomputable def polValue (B : BanditProcess N X) (σ : Policy N X) (x : ∀ j, X j)
    (s : Fin N → ℕ) (M : ℝ) : ℝ :=
  polValueFuel B σ (∑ i, s i) x s M

/-- The (finite-horizon) Gittins index rule of Theorem 1: at `(x, s)` it engages an active project
whose index `Mᵢ(xᵢ, sᵢ)` is maximal among the active projects, provided that maximal value exceeds
`M`, and otherwise retires. Ties among projects may be broken arbitrarily. -/
def IsIndexRule (B : BanditProcess N X) (σ : Policy N X) : Prop :=
  ∀ x s M,
    (∀ i, σ x s M = some i →
      0 < s i ∧ (∀ j, 0 < s j → index B j (x j) (s j) ≤ index B i (x i) (s i)) ∧
        M < index B i (x i) (s i)) ∧
    (σ x s M = none → ∀ j, 0 < s j → index B j (x j) (s j) ≤ M)

end WhittleGittins.Retirement
