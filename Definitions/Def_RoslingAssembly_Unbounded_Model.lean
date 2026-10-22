import Mathlib
import Definitions.Def_RoslingAssembly_SeriesEquiv_Policy

open MeasureTheory

namespace RoslingAssembly.Unbounded

/-- The data of Rosling's assembly model (§1, pp. 566–567): the number of items `N`
(items are `1, …, N`, item `1` is the end item), the immediate successor map `succ` (s(·), with
`s(1) = 0`), the lead times `l`, the echelon holding costs `h`, the backlogging cost `p`, the
installation holding cost `H1` of the end item, the discount factor `α` and the law `ν` of the
one-period demand ξ_t. Values of item-indexed functions outside `1, …, N` are never used.
No sign or positivity condition is built in. -/
structure Model where
  /-- number of items -/
  N : ℕ
  /-- immediate successor s(i) -/
  succ : ℕ → ℕ
  /-- lead time l_i -/
  l : ℕ → ℕ
  /-- echelon holding cost h_i -/
  h : ℕ → ℝ
  /-- backlogging cost p -/
  p : ℝ
  /-- installation holding cost H_1 of the end item -/
  H1 : ℝ
  /-- discount factor α -/
  α : ℝ
  /-- law of the one-period demand ξ_t -/
  ν : Measure ℝ

/-- The decisions of a policy are measurable functions of the observed history. -/
def IsMeasurablePolicy (π : RoslingAssembly.SeriesEquiv.Policy) : Prop :=
  ∀ (k : ℕ) (i : ℕ), Measurable fun x : Fin k → ℝ => π k x i

/-- Y_{i,k+1} along the demand path `ω`. -/
def Y (π : RoslingAssembly.SeriesEquiv.Policy) (ω : ℕ → ℝ) (k i : ℕ) : ℝ := π k (fun j => ω j) i

/-- The echelon position of item `i` in period `t = k + 1` ordered `s` periods ago or earlier,
along the demand path `ω`, from the initial data `x0`:
`Y_{i,t−s} − ∑_{r=t−s}^{t−1} ξ_r` if `s < t`, and `x0 i (s − t + 1) − ∑_{r=1}^{t−1} ξ_r` if `s ≥ t`.
Here `x0 i s` (`s ≥ 1`) is the echelon position of item `i` at the start of period 1 ordered
`s` periods ago or earlier. In particular X_it = `pos … i k 1`, X^l_it = `pos … i k (l i)`
and Y_it = `pos … i k 0`. -/
def pos (x0 : ℕ → ℕ → ℝ) (π : RoslingAssembly.SeriesEquiv.Policy) (ω : ℕ → ℝ) (i k s : ℕ) : ℝ :=
  if s ≤ k then Y π ω (k - s) i - ∑ r ∈ Finset.Ico (k - s) k, ω r
  else x0 i (s - k) - ∑ r ∈ Finset.range k, ω r

namespace Model

variable (S : Model)

/-- The items `1, …, N`. -/
def items : Finset ℕ := Finset.Icc 1 S.N

open Classical in
/-- A(i), the set of all successors of item `i`: the items `s^[n](i)`, `n ≥ 1`, reached along the
successor chain while it stays among the items (the chain stops at `s(1) = 0`). Under the tree
hypotheses the chain has at most `N` steps. -/
noncomputable def A (i : ℕ) : Finset ℕ :=
  S.items.filter fun k =>
    ∃ n ∈ Finset.Icc 1 S.N, S.succ^[n] i = k ∧ ∀ m ∈ Finset.range n, S.succ^[m] i ∈ S.items

/-- B(i), the set of all predecessors of item `i`: the items `k` with `i ∈ A(k)`. -/
noncomputable def B (i : ℕ) : Finset ℕ := S.items.filter fun k => i ∈ S.A k

/-- P(i), the set of immediate predecessors of item `i`: the items `k` with `s(k) = i`. -/
def P (i : ℕ) : Finset ℕ := S.items.filter fun k => S.succ k = i

/-- M_i, the total lead time of item `i` and all its successors (§2, p. 567):
`M_0 = 0` and `M_i = l_i + ∑_{k ∈ A(i)} l_k` for `i ≥ 1`. -/
noncomputable def M (i : ℕ) : ℕ := if i = 0 then 0 else S.l i + ∑ k ∈ S.A i, S.l k

/-- The tree hypotheses (§1, p. 566, and the indexing rule of §2, p. 567): `N ≥ 1`, `s(1) = 0`,
and every non-end item `i` has an immediate successor `s(i)` among the items with `s(i) < i`. -/
def IsTree : Prop :=
  1 ≤ S.N ∧ S.succ 1 = 0 ∧ ∀ i ∈ Finset.Icc 2 S.N, 1 ≤ S.succ i ∧ S.succ i < i

/-- The indexing rule `M_i ≥ M_{i−1}` for all items `i` (§2, p. 567). -/
def IsIndexed : Prop := ∀ i ∈ S.items, S.M (i - 1) ≤ S.M i

/-- The standing demand hypotheses (§1, p. 566): ξ_t ≥ 0, ξ_t has a density, and its mean
λ = E ξ_t is finite and positive. (Independence and identical distribution enter through the
product law `demandSeq`; that `ν` is a probability measure is a separate instance argument.) -/
def DemandStanding : Prop :=
  S.ν (Set.Iio 0) = 0 ∧ S.ν ≪ volume ∧ Integrable id S.ν ∧ 0 < ∫ x, x ∂S.ν

/-- The law of the demand sequence: coordinate `j` of `ω : ℕ → ℝ` is ξ_{j+1}, and the coordinates
are independent with common law `ν`. -/
noncomputable def demandSeq : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => S.ν

/-- The law of the demand over `l_1 + 1` periods, whose density is φ_1^{l+1} of (2). -/
noncomputable def leadDemandLaw : Measure ℝ :=
  (Measure.pi fun _ : Fin (S.l 1 + 1) => S.ν).map fun x => ∑ j, x j

/-- The expected backlog term ∫_Y^∞ (ξ − Y) φ_1^{l+1}(ξ) dξ of (2). -/
noncomputable def backlog (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂S.leadDemandLaw

/-- Well-formed initial data (taken for granted by the paper; it holds when the history before
period 1 consisted of nonnegative orders satisfying (3)): `x0 i` is antitone in the age `s ≥ 1`,
and `x0 i s ≤ x0 k (s + l_k)` for every predecessor `k ∈ P(i)` and every `s ≥ 1`. -/
def WellFormed (x0 : ℕ → ℕ → ℝ) : Prop :=
  (∀ i ∈ S.items, ∀ s, 1 ≤ s → x0 i (s + 1) ≤ x0 i s) ∧
  (∀ i ∈ S.items, ∀ k ∈ S.P i, ∀ s, 1 ≤ s → x0 i s ≤ x0 k (s + S.l k))

/-- Feasibility (3) from the initial data `x0`, almost surely: for almost every demand path,
in every period and for every item `i`, X_it ≤ Y_it ≤ X^l_kt for all `k ∈ P(i)`. -/
def Feasible (x0 : ℕ → ℕ → ℝ) (π : RoslingAssembly.SeriesEquiv.Policy) : Prop :=
  ∀ᵐ ω ∂S.demandSeq, ∀ k : ℕ, ∀ i ∈ S.items,
    pos x0 π ω i k 1 ≤ Y π ω k i ∧ ∀ j ∈ S.P i, Y π ω k i ≤ pos x0 π ω j k (S.l j)

/-- The one-period cost of (2) in period `t = k + 1` (without the constant):
`∑_{i=1}^N α^{l_i} h_i Y_it + α^{l_1} (p + H_1) ∫_{Y_1t}^∞ (ξ − Y_1t) φ_1^{l+1}(ξ) dξ`. -/
noncomputable def stageCost (π : RoslingAssembly.SeriesEquiv.Policy) (ω : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ S.items, S.α ^ S.l i * S.h i * Y π ω k i +
    S.α ^ S.l 1 * (S.p + S.H1) * S.backlog (Y π ω k 1)

/-- The objective (2) of Problem P without its policy-independent constant, as an extended real:
`E[∑_t (α^{t−1} c_t)⁺] − E[∑_t (α^{t−1} c_t)⁻]` (in `EReal`, `⊤ − ⊤ = ⊥`). -/
noncomputable def cost (π : RoslingAssembly.SeriesEquiv.Policy) : EReal :=
  ((∫⁻ ω, ∑' k, ENNReal.ofReal (S.α ^ k * S.stageCost π ω k) ∂S.demandSeq : ENNReal) : EReal) -
  ((∫⁻ ω, ∑' k, ENNReal.ofReal (-(S.α ^ k * S.stageCost π ω k)) ∂S.demandSeq : ENNReal) : EReal)

/-- The discounted echelon holding cost of item `i` and all its predecessors, the left-hand side
of Generalized Assumption (i) (§4, p. 571) and of the condition of Theorem 4(i) (p. 574):
`h_i α^{−M_{s(i)}} + ∑_{k ∈ B(i)} h_k α^{−M_{s(k)}}`. -/
noncomputable def echelonSum (i : ℕ) : ℝ :=
  S.h i * S.α ^ (-(S.M (S.succ i) : ℤ)) + ∑ k ∈ S.B i, S.h k * S.α ^ (-(S.M (S.succ k) : ℤ))

end Model

end RoslingAssembly.Unbounded
