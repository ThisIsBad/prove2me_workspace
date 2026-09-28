import Mathlib

namespace JacksonJobshop.Equilibrium

/-- Jackson's jobshop-like queueing system `(N, L, M, R)` (Management Science 10(1), 1963,
§§2–3, pp. 133–135), with its standing Assumptions (2.1)–(2.4).

* Centers are `Fin N`; the paper's Center `n` is `⟨n - 1, _⟩`.
* `lam K` is `λ(K)`, the arrival rate when `K` customers are present.
* `mu n k` is `μ(n, k)`, the service-completion rate at Center `n` holding `k` customers.
* `r : Option (Fin N) → Option (Fin N) → ℝ` encodes `R = {r(m, n) | m ∈ [0, N], n ∈ [1, N + 1]}`:
  in the first argument `none` is the paper's index `0` (start of a routing); in the second
  argument `none` is the paper's index `N + 1` (end of a routing). So `r none (some n) = r(0, n)`,
  `r (some m) none = r(m, N + 1)`, `r none none = r(0, N + 1)`, `r (some m) (some n) = r(m, n)`.
* `e n` is the solution `e(n)` of the traffic equations (2.5), assumed unique and
  non-negative by (2.4). -/
structure JobshopSystem (N : ℕ) where
  /-- arrival rates `λ(K)`, `K ∈ [0, ∞)` -/
  lam : ℕ → ℝ
  /-- service rates `μ(n, k)`, `n ∈ [1, N]`, `k ∈ [0, ∞)` -/
  mu : Fin N → ℕ → ℝ
  /-- routing probabilities `r(m, n)`, `m ∈ [0, N]`, `n ∈ [1, N + 1]` -/
  r : Option (Fin N) → Option (Fin N) → ℝ
  /-- the solution `e(n)` of equations (2.5) -/
  e : Fin N → ℝ
  /-- `N` is a positive integer (p. 133). -/
  N_pos : 0 < N
  /-- Assumption (2.1): either all `λ(K) > 0`, or for some `K₀ ≥ 0`, `λ(K) > 0` for `K ≤ K₀`
  and `λ(K) = 0` for `K > K₀`. -/
  lam_assumption :
    (∀ K, 0 < lam K) ∨ ∃ K₀ : ℕ, (∀ K, K ≤ K₀ → 0 < lam K) ∧ ∀ K, K₀ < K → lam K = 0
  /-- Assumption (2.2), first part: each `μ(n, 0) = 0`. -/
  mu_zero : ∀ n, mu n 0 = 0
  /-- Assumption (2.2), second part: all other `μ(n, k)` are positive. -/
  mu_pos : ∀ n k, 0 < k → 0 < mu n k
  /-- Assumption (2.3), non-negativity: each `{r(m, n) | n ∈ [1, N + 1]}` has non-negative
  entries. -/
  r_nonneg : ∀ m n, 0 ≤ r m n
  /-- Assumption (2.3), normalisation: for each `m ∈ [0, N]`, `Σ_{n ∈ [1, N+1]} r(m, n) = 1`. -/
  r_sum : ∀ m, ∑ n, r m n = 1
  /-- Assumption (2.4): `e` solves (2.5), `e(n) = r(0, n) + Σ_{m=1}^N e(m) r(m, n)`. -/
  e_traffic : ∀ n, e n = r none (some n) + ∑ m, e m * r (some m) (some n)
  /-- Assumption (2.4): the solution of (2.5) is unique. -/
  e_unique : ∀ e' : Fin N → ℝ,
    (∀ n, e' n = r none (some n) + ∑ m, e' m * r (some m) (some n)) → e' = e
  /-- Assumption (2.4): the `e(n)` are all non-negative. -/
  e_nonneg : ∀ n, 0 ≤ e n

variable {N : ℕ}

/-- `S(k) = k₁ + ⋯ + k_N`, the total number of customers in state `k` (p. 133). -/
def S (k : Fin N → ℕ) : ℕ := ∑ n, k n

/-- The stationary form (`dP/dt = 0`) of the balance equation (3.1) (p. 135) at the state `k`,
for a function `q` on state vectors, **with the arrival-outflow coefficient
`λ(S(k)) Σ_{n=1}^N r(0, n)`** given by the transition probabilities on p. 134 (the paper prints
`λ(S(k))` there, which disagrees with those transition probabilities when `r(0, N+1) > 0`).

Terms whose shifted state would have a negative component are omitted (they are guarded by
`0 < k n`, resp. `0 < k m`), and the double sum runs over ordered pairs `m ≠ n`.
* `h(n) = k` except its `n`th component is `k n - 1`;
* `l(n) = k` except its `n`th component is `k n + 1`;
* `j(m, n) = k` except its `m`th component is `k m - 1` and its `n`th is `k n + 1`. -/
def Balance (sys : JobshopSystem N) (q : (Fin N → ℕ) → ℝ) (k : Fin N → ℕ) : Prop :=
  0 = -((sys.lam (S k) * ∑ n, sys.r none (some n)) +
          ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * q k
    + ∑ n, (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * q (Function.update k n (k n - 1)) else 0)
    + ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q (Function.update k n (k n + 1))
    + ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) *
          q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0)

/-- An equilibrium state probability distribution (p. 135): a probability distribution
`{q(k)}` over state vectors such that `P(k, t) ≡ q(k)` is a constant solution of (3.1). -/
def IsEquilibrium (sys : JobshopSystem N) (q : (Fin N → ℕ) → ℝ) : Prop :=
  (∀ k, 0 ≤ q k) ∧ HasSum q 1 ∧ ∀ k, Balance sys q k

/-- (4.1) `W(K) = Π_{i=0}^{K-1} λ(i)` (empty product `1`). -/
def W (sys : JobshopSystem N) (K : ℕ) : ℝ := ∏ i ∈ Finset.range K, sys.lam i

/-- (4.2) `w(k) = Π_{n=1}^N Π_{i=1}^{k_n} [e(n)/μ(n, i)]` (empty products `1`). -/
noncomputable def w (sys : JobshopSystem N) (k : Fin N → ℕ) : ℝ :=
  ∏ n, ∏ i ∈ Finset.Icc 1 (k n), sys.e n / sys.mu n i

/-- (4.3) `T(K) = Σ_{S(k) = K} w(k)`, a finite sum over state vectors with total `K`. -/
noncomputable def T (sys : JobshopSystem N) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple N K, w sys k

open scoped Classical in
/-- (4.4) `π = {Σ_{K=0}^∞ W(K) T(K)}⁻¹` if the sum converges, `= 0` otherwise. -/
noncomputable def piConst (sys : JobshopSystem N) : ℝ :=
  if Summable (fun K => W sys K * T sys K) then (∑' K, W sys K * T sys K)⁻¹ else 0

/-- (4.6) `p(k) = π w(k) W(S(k))`. -/
noncomputable def productForm (sys : JobshopSystem N) (k : Fin N → ℕ) : ℝ :=
  piConst sys * w sys k * W sys (S k)

/-- (6.1) in the case `k_n* = +∞`: `w_n(k) = Π_{i=1}^k [λ(0) e(n)/μ(n, i)]`. -/
noncomputable def wn (sys : JobshopSystem N) (n : Fin N) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 k, sys.lam 0 * sys.e n / sys.mu n i

open scoped Classical in
/-- (6.2) `p_n(k) = w_n(k) / Σ_{i=0}^∞ w_n(i)` if the sum converges, `= 0` otherwise. -/
noncomputable def pn (sys : JobshopSystem N) (n : Fin N) (k : ℕ) : ℝ :=
  if Summable (fun i => wn sys n i) then wn sys n k / ∑' i, wn sys n i else 0

end JacksonJobshop.Equilibrium
