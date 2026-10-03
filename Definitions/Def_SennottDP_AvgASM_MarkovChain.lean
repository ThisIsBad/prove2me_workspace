import Mathlib

namespace SennottDP.AvgASM

open scoped ENNReal NNReal
open Filter Topology

/-! Markov chains with costs (Sennott, Appendix C.1–C.3, pp. 292–302). A Markov chain `Γ` on a
countable state space `T` is given by its transition matrix `Q : T → T → ℝ≥0∞`, and a cost
function `c : T → ℝ≥0∞` (in this mission always the coercion of a finite nonnegative cost). -/

variable {T : Type*} [Countable T]

open Classical in
/-- The `t`-step transition probabilities `P^{(t)}_{ij}`, with `P^{(0)}_{ij} = δ_{ij}`
(App. C.1, p. 292). -/
noncomputable def nStep (Q : T → T → ℝ≥0∞) : ℕ → T → T → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, nStep Q t i k * Q k j

open Classical in
/-- The taboo probability `_G P^{(t)}_{ik}` (App. C.1, p. 295): the probability of going from `i`
to `k` in `t` transitions without visiting `G` at the intermediate times `1, …, t − 1`, **and**
(for `t ≥ 1`) with `k ∉ G`. Equivalently `P(X_t = k, T_{iG} > t | X_0 = i)` where `T_{iG} ≥ 1` is
the first passage time from `i` to `G`. (The book's `_G P^{(t)}_{ik}` allows `k ∈ G`; the
quantity here is its restriction to `k ∉ G`, which is all that the first passage moments below
use.) -/
noncomputable def avoidProb (Q : T → T → ℝ≥0∞) (G : Set T) : ℕ → T → T → ℝ≥0∞
  | 0, i, k => if i = k then 1 else 0
  | t + 1, i, k => if k ∈ G then 0 else ∑' j, avoidProb Q G t i j * Q j k

/-- The expected first passage time `m_{iG} = E[T_{iG}]` from `i` to `G` (p. 295), computed as
`∑_{t ≥ 0} P(T_{iG} > t)`. It is `∞` whenever `P(T_{iG} < ∞) < 1`, as in the book. -/
noncomputable def meanPassage (Q : T → T → ℝ≥0∞) (G : Set T) (i : T) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, avoidProb Q G t i k

/-- The expected cost of a first passage from `i` to `G` (p. 298),
`c_{iG} = E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i] = ∑_{t ≥ 0} ∑_k P(X_t = k, T_{iG} > t) C(k)`.
The book uses `c_{iG}` only when `m_{iG} < ∞`, where this is the expected first passage cost. -/
noncomputable def passageCost (Q : T → T → ℝ≥0∞) (c : T → ℝ≥0∞) (G : Set T) (i : T) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, avoidProb Q G t i k * c k

/-- `i` leads to `j`: `P^{(t)}_{ij} > 0` for some `t ≥ 0` (p. 293). -/
def LeadsTo (Q : T → T → ℝ≥0∞) (i j : T) : Prop :=
  ∃ t, 0 < nStep Q t i j

/-- `i` and `j` communicate (p. 293). -/
def Communicate (Q : T → T → ℝ≥0∞) (i j : T) : Prop :=
  LeadsTo Q i j ∧ LeadsTo Q j i

/-- `i` is positive recurrent: the expected return time `m_{ii}` is finite (p. 293; this forces
`P(T_{ii} < ∞) = 1`). -/
def PositiveRecurrent (Q : T → T → ℝ≥0∞) (i : T) : Prop :=
  meanPassage Q {i} i < ⊤

/-- `R` is a positive recurrent class: the communicating class of a positive recurrent state
(p. 293; positive recurrence is a class property). -/
def IsPosRecClass (Q : T → T → ℝ≥0∞) (R : Set T) : Prop :=
  ∃ i, PositiveRecurrent Q i ∧ R = {j | Communicate Q i j}

/-- The steady state probability `π_j = (m_{jj})^{-1}`, interpreted as `0` when `m_{jj} = ∞`
(p. 294). -/
noncomputable def steadyState (Q : T → T → ℝ≥0∞) (j : T) : ℝ≥0∞ :=
  (meanPassage Q {j} j)⁻¹

/-- A positive recurrent class `R` is aperiodic if `π_j = lim_{n→∞} P^{(n)}_{ij}` for `i, j ∈ R`
(p. 295). -/
def IsAperiodicClass (Q : T → T → ℝ≥0∞) (R : Set T) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, Tendsto (fun n => nStep Q n i j) atTop (𝓝 (steadyState Q j))

/-- `Γ` is unichain (a single positive recurrent class, p. 302) and its positive recurrent class
contains `z`. -/
def IsUnichainWith (Q : T → T → ℝ≥0∞) (z : T) : Prop :=
  ∃ R, IsPosRecClass Q R ∧ z ∈ R ∧ ∀ R', IsPosRecClass Q R' → R' = R

/-- `Γ` is unichain with an aperiodic positive recurrent class containing `z` (Step 1 of
Proposition 8.2.1, p. 171). -/
def IsUnichainAperiodicWith (Q : T → T → ℝ≥0∞) (z : T) : Prop :=
  ∃ R, IsPosRecClass Q R ∧ z ∈ R ∧ IsAperiodicClass Q R ∧ ∀ R', IsPosRecClass Q R' → R' = R

/-- Definition C.2.5, p. 301: `Γ` is `z` standard if `m_{iz} < ∞` and `c_{iz} < ∞` for all
`i ∈ S`. -/
def IsStandard (Q : T → T → ℝ≥0∞) (c : T → ℝ≥0∞) (z : T) : Prop :=
  ∀ i, meanPassage Q {z} i < ⊤ ∧ passageCost Q c {z} i < ⊤

/-- The average cost of the Markov chain with costs from `X_0 = i`,
`J(i) = limsup_{n→∞} J^{(n)}_i`, `J^{(n)}_i = (1/n) ∑_{t=0}^{n-1} ∑_j P^{(t)}_{ij} C(j)`
((C.11), p. 298), in `[0, ∞]`. On a positive recurrent class `R` it is the constant `J_R`
(Proposition C.2.1(i)). -/
noncomputable def chainAvgCost (Q : T → T → ℝ≥0∞) (c : T → ℝ≥0∞) (i : T) : ℝ≥0∞ :=
  limsup (fun n : ℕ => (∑ t ∈ Finset.range n, ∑' j, nStep Q t i j * c j) / (n : ℝ≥0∞)) atTop

end SennottDP.AvgASM
