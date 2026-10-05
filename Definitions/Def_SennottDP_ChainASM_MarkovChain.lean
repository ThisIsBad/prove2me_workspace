import Mathlib

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.ChainASM

/-! Markov chains with costs (Sennott 1999, Appendix C.1–C.2, pp. 292–301). A Markov chain `Γ`
on a countable state space `S` is a transition matrix `P` whose rows are probability
distributions, together with a finite nonnegative cost `C(i)` at every state. All probabilistic
quantities are computed from `P` alone, in `[0, ∞]`. -/

/-- A Markov chain with costs `Γ` on the state space `S` (pp. 292 and 298): transition
probabilities `P_{ij}` with `∑_j P_{ij} = 1` for every `i`, and a finite nonnegative cost `C(i)`
attached to each state. -/
structure MC (S : Type*) where
  /-- the transition probability `P_{ij}` -/
  P : S → S → ℝ≥0∞
  /-- each row is a probability distribution: `∑_j P_{ij} = 1` -/
  P_sum : ∀ i, ∑' j, P i j = 1
  /-- the (finite, nonnegative) cost `C(i)` -/
  C : S → ℝ≥0

namespace MC

variable {S : Type*} (Γ : MC S)

open Classical in
/-- The `t`-step transition probabilities `P^{(t)}_{ij}`, `P^{(0)}_{ij} = δ_{ij}` (p. 292). -/
noncomputable def nStep : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, nStep t i k * Γ.P k j

open Classical in
/-- The taboo probability `_G P^{(t)}_{ik}` (p. 295): the probability of going from `i` to `k` in
`t` slots with none of the intermediate states `X_1, …, X_{t-1}` in `G` (the initial and the
terminal state may lie in `G`). `_G P^{(0)}_{ik} = δ_{ik}`, `_G P^{(1)}_{ik} = P_{ik}`, and
`_G P^{(t+1)}_{ik} = ∑_{j ∉ G} P_{ij} {}_G P^{(t)}_{jk}` for `t ≥ 1` ((C.2), p. 296). -/
noncomputable def tabooProb (G : Set S) : ℕ → S → S → ℝ≥0∞
  | 0, i, k => if i = k then 1 else 0
  | 1, i, k => Γ.P i k
  | t + 2, i, k => ∑' j, if j ∈ G then 0 else Γ.P i j * tabooProb G (t + 1) j k

open Classical in
/-- `P(X_t = k, T_{iG} > t | X_0 = i)`, where `T_{iG} ≥ 1` is the first passage time from `i`
to the nonempty set `G` (p. 295): `δ_{ik}` for `t = 0`, and for `t ≥ 1` the taboo probability
`_G P^{(t)}_{ik}` restricted to `k ∉ G`. -/
noncomputable def avoidProb (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  if t = 0 then (if i = k then 1 else 0) else if k ∈ G then 0 else Γ.tabooProb G t i k

/-- `_G u_{ik}`, the expected number of visits to `k` during a first passage from `i` to `G`
(p. 295): the visits at the times `0 ≤ t < T_{iG}`, i.e. `∑_{t ≥ 0} P(X_t = k, T_{iG} > t)`.
For `k ∈ G` this is `δ_{ik}` (so `0` if `i ∉ G`), and for `k ∉ G` it is
`δ_{ik} + ∑_{t ≥ 1} {}_G P^{(t)}_{ik}`. -/
noncomputable def visits (G : Set S) (i k : S) : ℝ≥0∞ :=
  ∑' t : ℕ, Γ.avoidProb G t i k

/-- `m_{iG} = E[T_{iG}]`, the expected first passage time from `i` to `G` (p. 295), computed as
`∑_{t ≥ 0} P(T_{iG} > t)`. It equals `∞` whenever `P(T_{iG} < ∞) < 1`, as in the book.
`m_{ij}` is `m_{i\{j\}}`. -/
noncomputable def meanPassage (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, Γ.avoidProb G t i k

/-- `c_{iG}`, the expected cost of a first passage from `i` to `G` (p. 298):
`E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i] = ∑_{t ≥ 0} ∑_k P(X_t = k, T_{iG} > t) C(k)`. The book
speaks of `c_{iG}` only when `m_{iG} < ∞`; there it is this quantity. -/
noncomputable def passageCost (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, Γ.avoidProb G t i k * (Γ.C k : ℝ≥0∞)

/-- `i` leads to `j`: `P^{(t)}_{ij} > 0` for some `t ≥ 0` (p. 293). -/
def LeadsTo (i j : S) : Prop :=
  ∃ t, 0 < Γ.nStep t i j

/-- `i` and `j` communicate (p. 293). -/
def Communicate (i j : S) : Prop :=
  Γ.LeadsTo i j ∧ Γ.LeadsTo j i

/-- The communicating class of `z`. -/
def commClass (z : S) : Set S :=
  {j | Γ.Communicate z j}

/-- `Γ` is irreducible: all states communicate (p. 293). -/
def Irreducible : Prop :=
  ∀ i j, Γ.Communicate i j

/-- `i` is positive recurrent: the expected return time `m_{ii}` is finite (p. 293; finiteness
of `m_{ii}` forces `P(T < ∞) = 1`). A state is transient or null recurrent exactly when
`m_{ii} = ∞`. -/
def PosRecurrent (i : S) : Prop :=
  Γ.meanPassage {i} i < ⊤

/-- `R` is a positive recurrent class: the communicating class of a positive recurrent state
(p. 293; positive recurrence is a class property). -/
def IsPosRecClass (R : Set S) : Prop :=
  ∃ i, Γ.PosRecurrent i ∧ R = Γ.commClass i

/-- The steady state probability `π_j = (m_{jj})^{-1}`, which is `0` when `m_{jj} = ∞` (p. 294). -/
noncomputable def steadyState (j : S) : ℝ≥0∞ :=
  (Γ.meanPassage {j} j)⁻¹

/-- The average cost from `X_0 = i`, `J(i) = limsup_{n→∞} J^{(n)}_i` with
`J^{(n)}_i = (1/n) E[∑_{t=0}^{n-1} C(X_t) | X_0 = i] = ∑_j C(j) Q^{(n)}_{ij}` ((C.11), p. 298),
a value in `[0, ∞]`. (On a positive recurrent class and on a finite state space the limit
exists, Proposition C.2.1(i) and Section C.3.) -/
noncomputable def avgCost (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ =>
    (∑ t ∈ Finset.range n, ∑' j, Γ.nStep t i j * (Γ.C j : ℝ≥0∞)) / (n : ℝ≥0∞)) atTop

/-- The average cost on a positive recurrent class `R`, `J_R = ∑_{j ∈ R} π_j C(j)`
(Proposition C.2.1(i), p. 298), a value in `[0, ∞]`. -/
noncomputable def classAvgCost (R : Set S) : ℝ≥0∞ :=
  ∑' j : R, Γ.steadyState j * (Γ.C j : ℝ≥0∞)

/-- Definition C.2.5, p. 301: `Γ` is `z` standard if `m_{iz} < ∞` and `c_{iz} < ∞` for all
`i ∈ S`. -/
def IsZStandard (z : S) : Prop :=
  ∀ i, Γ.meanPassage {z} i < ⊤ ∧ Γ.passageCost {z} i < ⊤

/-- `Γ` is unichain (exactly one positive recurrent class, p. 302) and `z` is an element of its
positive recurrent class. -/
def IsUnichainWith (z : S) : Prop :=
  ∃ R, Γ.IsPosRecClass R ∧ z ∈ R ∧ ∀ R', Γ.IsPosRecClass R' → R' = R

end MC

end SennottDP.ChainASM
