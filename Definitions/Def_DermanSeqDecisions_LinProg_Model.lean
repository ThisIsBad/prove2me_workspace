import Mathlib

namespace DermanSeqDecisions.LinProg

/-! Derman's sequential decision model restricted to the class `C′` of stationary randomized
procedures (Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24
(1962), DOI 10.1287/mnsc.9.1.16, §1, pp. 16–17, and §3, pp. 20–21).

**Formalization Note.** The states `0, ⋯, L` are a finite type (`S`, or `I` when the state set of
§3 may also be the augmented set `{−1, 0, ⋯, L}`), the decisions `d_1, ⋯, d_K` a finite type
`Act`; every decision is available in every state, as in the paper. Probabilities and costs are
real numbers. -/

open Matrix Filter

open scoped ENNReal

section Basic

variable {I Act : Type*}

/-- The chance laws `q_{ij}(k)` (p. 16): for every state `i` and decision `k`, `q_{i·}(k)` is a
probability vector, `q_{ij}(k) ≥ 0` and `∑_j q_{ij}(k) = 1`. -/
def IsTransitionLaw [Fintype I] (q : I → Act → I → ℝ) : Prop :=
  (∀ i a j, 0 ≤ q i a j) ∧ ∀ i a, ∑ j, q i a j = 1

/-- A procedure of class `C′` (p. 17): `D_{ik}` is the probability of making decision `d_k` when the
system is observed in state `i`, independently of the past and of the time, so `D_{ik} ≥ 0` and
`∑_k D_{ik} = 1`. -/
def IsStationaryRandomized [Fintype Act] (D : I → Act → ℝ) : Prop :=
  (∀ i a, 0 ≤ D i a) ∧ ∀ i, ∑ a, D i a = 1

/-- The transition matrix of the Markov chain `{X_t}` under a procedure `D ∈ C′` (p. 17):
`p_{ij} = ∑_k q_{ij}(k) D_{ik}`. -/
def chainMatrix [Fintype Act] (q : I → Act → I → ℝ) (D : I → Act → ℝ) : Matrix I I ℝ :=
  Matrix.of fun i j => ∑ a, q i a j * D i a

variable [Fintype I] [DecidableEq I] [Fintype Act]

/-- The expected cost `W_t` ascribed to time `t` under `D ∈ C′` when `X_0 = i` (p. 17):
`W_t = ∑_j p^{(t)}_{ij} ∑_k D_{jk} w_{jk}`, where `p^{(t)}` is the `t`-step transition matrix. -/
def expCost (q : I → Act → I → ℝ) (w : I → Act → ℝ) (D : I → Act → ℝ) (i : I) (t : ℕ) : ℝ :=
  ∑ j, (chainMatrix q D ^ t) i j * ∑ a, D j a * w j a

/-- Problem 1's criterion (p. 17): `Q_R(i) = limsup_{T→∞} (1/T) ∑_{t=0}^T W_t`, with the paper's
own indexing (the sum runs over `t = 0, ⋯, T`). It is a real `limsup`; for a transition law and a
procedure of `C′` the sequence is bounded by `max |w_{jk}|` (for `T ≥ 1`; the `T = 0` term is `0`),
so the value is the true upper limit. -/
noncomputable def avgCost (q : I → Act → I → ℝ) (w : I → Act → ℝ) (D : I → Act → ℝ) (i : I) :
    ℝ :=
  limsup (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range (T + 1), expCost q w D i t) atTop

/-- Problem 2's criterion (p. 17): `S_R(i) = ∑_{t=0}^∞ W_t`, "possibly ∞", in `ℝ≥0∞`. In Problem 2
the costs are nonnegative, so `W_t ≥ 0` and `ENNReal.ofReal` loses nothing. -/
noncomputable def totalCost (q : I → Act → I → ℝ) (w : I → Act → ℝ) (D : I → Act → ℝ) (i : I) :
    ℝ≥0∞ :=
  ∑' t, ENNReal.ofReal (expCost q w D i t)

/-- The taboo probability `_i p^{(t)}_{ij}` of a transition matrix `P` (p. 20): the probability
that `X_t = j` and `X_s ≠ i` for `0 < s < t`, given `X_0 = i`; by the paper's convention
`_i p^{(0)}_{ij} = 0`. So `_i p^{(1)}_{ij} = p_{ij}` and
`_i p^{(t+1)}_{ij} = ∑_{l ≠ i} {}_i p^{(t)}_{il} p_{lj}` for `t ≥ 1`. -/
def tabooProb (P : Matrix I I ℝ) (i : I) : ℕ → I → ℝ
  | 0 => fun _ => 0
  | 1 => fun j => P i j
  | t + 2 => fun j => ∑ l, (if l = i then 0 else tabooProb P i (t + 1) l) * P l j

/-- The constraints (10) (p. 21) on the state-action frequencies `x_{jk}`, `j ∈ I`:
`x_{jk} ≥ 0`, `∑_k x_{jk} − ∑_{i ∈ I} ∑_k x_{ik} q_{ij}(k) = 0` for every `j ∈ I`, and
`∑_{j ∈ I} ∑_k x_{jk} = 1`. -/
def IsFreqSolution (q : I → Act → I → ℝ) (x : I → Act → ℝ) : Prop :=
  (∀ j k, 0 ≤ x j k) ∧ (∀ j, ∑ k, x j k - ∑ i, ∑ k, x i k * q i k j = 0) ∧
    ∑ j, ∑ k, x j k = 1

/-- The objective (8): `∑_j ∑_k x_{jk} w_{jk}`. -/
def freqObjective (w : I → Act → ℝ) (x : I → Act → ℝ) : ℝ :=
  ∑ j, ∑ k, x j k * w j k

/-- The procedure decoded from frequencies (p. 21): `D_{jk} = x_{jk} / ∑_k x_{jk}`. (Junk `0` where
`∑_k x_{jk} = 0`; on solutions of (10) under Assumption A the row sums are positive.) -/
noncomputable def decode (x : I → Act → ℝ) : I → Act → ℝ :=
  fun j k => x j k / ∑ k', x j k'

/-- The coefficient matrix of (10) written as a system `∑_{(i,k)} a_{r,(i,k)} x_{ik} = b_r`, one row
`r = j ∈ I` per balance equation, `a_{j,(i,k)} = [i = j] − q_{ij}(k)`, and one row `r = none` for the
normalization, `a_{none,(i,k)} = 1`. -/
def freqRowMatrix (q : I → Act → I → ℝ) : Option I → I × Act → ℝ
  | some j, p => (if p.1 = j then 1 else 0) - q p.1 p.2 j
  | none, _ => 1

/-- The right-hand side of (10) in the form of `freqRowMatrix`: `0` on the balance rows, `1` on the
normalization row. -/
def freqRhs : Option I → ℝ
  | some _ => 0
  | none => 1

end Basic

section Augmented

variable {S Act : Type*}

/-- The chance law of Problem 2 with the adjoined state `−1` (`none`) (p. 21). The paper sets, for
every `R ∈ C′`, `p_{−1,i} = 1/(L+1)` for `i = 0, ⋯, L`, `p_{i,−1} = 0` for `i = 0, ⋯, L − 1` and
`p_{L,−1} = 1`. These are the transition probabilities of every `D ∈ C′` for the law below: from
`−1` every decision moves to each of `0, ⋯, L` with probability `1/(L+1)`; from `L` every decision
moves to `−1` (the absorbing row of `L` is replaced); from `i ≠ L` the law is `q_{ij}(k)`. -/
noncomputable def augLaw [Fintype S] [DecidableEq S] (q : S → Act → S → ℝ) (L : S) :
    Option S → Act → Option S → ℝ
  | none, _, none => 0
  | none, _, some _ => 1 / (Fintype.card S : ℝ)
  | some i, _, none => if i = L then 1 else 0
  | some i, a, some j => if i = L then 0 else q i a j

/-- The costs of the augmented problem (p. 21): `w_{−1,k} = 0`, and `w_{ik}` on the original
states. -/
def augCost (w : S → Act → ℝ) : Option S → Act → ℝ
  | none, _ => 0
  | some i, a => w i a

/-- A procedure of `C′` on the original states, extended to `−1` by the decision probabilities
`D₀` (they do not affect the augmented chain, whose row at `−1` is the same for every decision). -/
def augProc (D : S → Act → ℝ) (D₀ : Act → ℝ) : Option S → Act → ℝ
  | none => D₀
  | some i => D i

/-- The vector `(d_{(j,k)})` of the Lemma applied to (9): `d_{(−1,k)} = 1` and `d_{(j,k)} = 0` for
`j ≠ −1`, so that `∑ d_{(j,k)} x_{jk} = ∑_k x_{−1,k}`, the denominator of (9). -/
def cycleDenom : Option S × Act → ℝ :=
  fun p => if p.1 = none then 1 else 0

/-- The objective `h` of the Lemma applied to (9): `c_{(j,k)} = w_{jk}` with `w_{−1,k} = 0`, so that
`∑ c_{(j,k)} x_{jk}` is the numerator of (9). -/
def cycleCost (w : S → Act → ℝ) : Option S × Act → ℝ :=
  fun p => augCost w p.1 p.2

/-- The procedure on the original states `0, ⋯, L` read off a point `(z, z_{n+1})` of (12) for
Problem 2: `x = z / z_{n+1}` (the inverse transformation of the Lemma, p. 23), then
`D_{jk} = x_{jk} / ∑_k x_{jk}` (p. 21), restricted to `j ≠ −1`. -/
noncomputable def decodeCycle [Fintype S] [DecidableEq S] [Fintype Act] (z : Option S × Act → ℝ) (zlast : ℝ) : S → Act → ℝ :=
  fun i k => decode (fun j k' => z (j, k') / zlast) (some i) k

end Augmented

end DermanSeqDecisions.LinProg
