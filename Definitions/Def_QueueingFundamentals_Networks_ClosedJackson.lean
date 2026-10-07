import Mathlib

namespace QueueingFundamentals.Networks

open Finset

/-- The state space of a closed network of `k` nodes with `N` customers (§4.3, p.196):
all `n̄ = (n_1, …, n_k)` with `n_i ∈ ℕ` and `n_1 + ⋯ + n_k = N`. Nodes are indexed by `Fin k`
(book node `i` is index `i - 1`). -/
def states (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (N + 1)).filter fun n => ∑ i, n i = N

/-- A routing matrix of a closed network (§4.3, p.195: `γ_i = 0`, `r_i0 = 0`): the entries
`r_ij` are routing probabilities, `r_ij ≥ 0`, and each row sums to one. -/
def IsRoutingMatrix {k : ℕ} (R : Fin k → Fin k → ℝ) : Prop :=
  (∀ i j, 0 ≤ R i j) ∧ ∀ i, ∑ j, R i j = 1

/-- The routing matrix is irreducible (p.196): every node can be reached from every node
through routing steps of positive probability. -/
def IsIrreducible {k : ℕ} (R : Fin k → Fin k → ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < R a b) i j

/-- The traffic equations (4.16), p.196, of a closed network:
`μ_i ρ_i = ∑_{j=1}^{k} μ_j r_ji ρ_j` for every node `i`. -/
def IsTrafficSolution {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (rho : Fin k → ℝ) : Prop :=
  ∀ i, mu i * rho i = ∑ j, mu j * R j i * rho j

/-- The visit-ratio equations (4.25), p.202: `v_i = ∑_{j=1}^{k} v_j r_ji` for every node `i`. -/
def IsVisitRatio {k : ℕ} (R : Fin k → Fin k → ℝ) (v : Fin k → ℝ) : Prop :=
  ∀ i, v i = ∑ j, v j * R j i

/-- The state `n̄; i⁺j⁻` of Table 4.2, p.188: one more customer at node `i`, one fewer at node `j`
(used only for `i ≠ j` and `n_j ≥ 1`). -/
def moveState {k : ℕ} (n : Fin k → ℕ) (i j : Fin k) : Fin k → ℕ :=
  Function.update (Function.update n j (n j - 1)) i (n i + 1)

/-- The steady-state flow-balance equations (4.14), p.196, of a closed Jackson network with a
single exponential server of rate `μ_i` at each node, at the state `n̄`:
`∑_{j=1}^{k} ∑_{i ≠ j} μ_i r_ij p_{n̄;i⁺j⁻} = ∑_{i=1}^{k} μ_i (1 − r_ii) p_{n̄}`,
with the book's convention (p.188) that terms with a negative subscript and terms `μ_i` with
`n_i = 0` are zero. -/
def BalanceAt {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (p : (Fin k → ℕ) → ℝ)
    (n : Fin k → ℕ) : Prop :=
  (∑ j, ∑ i ∈ univ.filter (fun i => i ≠ j),
      if 1 ≤ n j then mu i * R i j * p (moveState n i j) else 0) =
    ∑ i, if 1 ≤ n i then mu i * (1 - R i i) * p n else 0

/-- A steady-state distribution of the `N`-customer closed Jackson network with single servers
(§1.9 and §4.3): a probability distribution on the states with `n_1 + ⋯ + n_k = N` (zero
elsewhere) that satisfies the balance equations (4.14) at every such state. -/
def IsClosedSteadyState {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ (∀ n, n ∉ states k N → p n = 0) ∧ (∑ n ∈ states k N, p n) = 1 ∧
    ∀ n ∈ states k N, BalanceAt mu R p n

/-- The marginal probability `p_i(m; N) = Pr{N_i = m | N customers in network}` (p.208) of a
distribution `p` on the `N`-customer states. -/
noncomputable def marginal {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) (m : ℕ) : ℝ :=
  ∑ n ∈ (states k N).filter (fun n => n i = m), p n

/-- The complementary marginal `P̄_i(m; N) = Pr{N_i ≥ m | N customers in network}` (p.208). -/
noncomputable def tailMarginal {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) (m : ℕ) : ℝ :=
  ∑ n ∈ (states k N).filter (fun n => m ≤ n i), p n

/-- The throughput of node `i` (p.209): `λ_i(N) = Pr{server busy at node i} · μ_i = P̄_i(1; N) μ_i`. -/
noncomputable def throughput {k : ℕ} (mu : Fin k → ℝ) (N : ℕ) (p : (Fin k → ℕ) → ℝ)
    (i : Fin k) : ℝ :=
  tailMarginal N p i 1 * mu i

/-- The mean number `L_i(N) = ∑_n n p_i(n; N)` of customers at node `i` (p.201, p.204). -/
noncomputable def meanNumber {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) : ℝ :=
  ∑ n ∈ states k N, (n i : ℝ) * p n

/-- The multiserver factor `a_i(n_i)` of (4.13), p.191, for a node with `c` servers:
`a(n) = n!` for `n < c` and `a(n) = c^{n−c} c!` for `n ≥ c`. For `c = 1` it is identically `1`. -/
noncomputable def serverFactor (c n : ℕ) : ℝ :=
  if n < c then (n.factorial : ℝ) else (c : ℝ) ^ (n - c) * (c.factorial : ℝ)

/-- Buzen's factors `f_i(n_i) = ρ_i^{n_i} / a_i(n_i)` (p.198) for a closed network with `c_i`
servers at node `i`. -/
noncomputable def buzenFactor {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (i : Fin k) (n : ℕ) : ℝ :=
  rho i ^ n / serverFactor (c i) n

/-- The normalizing constant (4.18)/(4.19), p.197–198:
`G(N) = ∑_{n_1+⋯+n_k=N} ∏_{i=1}^{k} f_i(n_i)`. -/
noncomputable def normConst {k : ℕ} (f : Fin k → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ states k N, ∏ i, f i (n i)

/-- Buzen's auxiliary function (4.20), p.199, over the first `m ≤ k` nodes:
`g_m(n) = ∑_{n_1+⋯+n_m=n} ∏_{i=1}^{m} f_i(n_i)`. For `m = 0` it is `1` at `n = 0` and `0` otherwise
(the empty network). -/
noncomputable def gBuzen {k : ℕ} (f : Fin k → ℕ → ℝ) (m : ℕ) (hm : m ≤ k) (n : ℕ) : ℝ :=
  ∑ x ∈ states m n, ∏ i : Fin m, f (Fin.castLE hm i) (x i)

/-- The product-form distribution (4.15)/(4.17), p.196: `p_{n̄} = (1/G(N)) ∏_{i=1}^{k} f_i(n_i)` on
the states with `n_1 + ⋯ + n_k = N`, and `0` elsewhere. With `f_i(n) = ρ_i^n` it is (4.15), with
`f_i(n) = ρ_i^n / a_i(n)` it is (4.17). -/
noncomputable def productForm {k : ℕ} (f : Fin k → ℕ → ℝ) (N : ℕ) (n : Fin k → ℕ) : ℝ :=
  if n ∈ states k N then (∏ i, f i (n i)) / normConst f N else 0

end QueueingFundamentals.Networks
