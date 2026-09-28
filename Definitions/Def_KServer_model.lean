import Mathlib

namespace KServer

/-- A **configuration** of `k` labeled servers in the metric space `M`:
server `i` sits at the point `C i`. -/
abbrev Config (k : ℕ) (M : Type*) := Fin k → M

/-- The **movement cost** from configuration `C` to configuration `C'`:
each server `i` travels from `C i` to `C' i`, and the cost is the total
distance traveled by all servers. -/
noncomputable def moveCost {k : ℕ} {M : Type*} [MetricSpace M]
    (C C' : Config k M) : ℝ :=
  ∑ i, dist (C i) (C' i)

/-- A **deterministic online `k`-server algorithm** on the metric space `M`.
`conf l` is the configuration of the servers after serving the request
sequence `l` (in order); `conf []` is the initial configuration. Because the
configuration is a function of the request prefix alone, the algorithm is by
construction deterministic and online: it never sees future requests.
`serves` demands that immediately after each new request `r`, some server
is located at `r`. -/
structure OnlineAlgorithm (k : ℕ) (M : Type*) [MetricSpace M] where
  conf : List M → Config k M
  serves : ∀ (l : List M) (r : M), ∃ i, conf (l ++ [r]) i = r

/-- The total movement cost incurred by the online algorithm `A` on the
request sequence `σ`: the sum, over the requests of `σ`, of the movement
cost between the configurations before and after serving each request. -/
noncomputable def OnlineAlgorithm.cost {k : ℕ} {M : Type*} [MetricSpace M]
    (A : OnlineAlgorithm k M) (σ : List M) : ℝ :=
  ∑ j ∈ Finset.range σ.length,
    moveCost (A.conf (σ.take j)) (A.conf (σ.take (j + 1)))

/-- `ServesFrom C₀ σ S`: the (offline) schedule `S` starts at the initial
configuration `C₀` (that is, `S 0 = C₀`) and serves the request sequence `σ`:
for each `j`, some server of the configuration `S (j+1)` is located at the
`j`-th request of `σ`. Values of `S` beyond `σ.length` are irrelevant. -/
def ServesFrom {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (S : ℕ → Config k M) : Prop :=
  S 0 = C₀ ∧ ∀ j : Fin σ.length, ∃ i, S (j + 1) i = σ.get j

/-- The **optimal offline cost** of serving the request sequence `σ` starting
from the configuration `C₀`: the infimum, over all schedules serving `σ` from
`C₀`, of the total movement cost. The offline schedule knows the whole of `σ`
in advance. -/
noncomputable def offlineCost {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ℝ :=
  sInf {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}

/-- The online algorithm `A` is **`c`-competitive** if there is a constant
`a` (which may depend on `A`, hence on its metric space and its initial
configuration, but not on the request sequence) such that on every request
sequence the cost of `A` is at most `c` times the optimal offline cost from
`A`'s initial configuration, plus `a`. -/
def IsCompetitive {k : ℕ} {M : Type*} [MetricSpace M]
    (A : OnlineAlgorithm k M) (c : ℝ) : Prop :=
  ∃ a : ℝ, ∀ σ : List M, A.cost σ ≤ c * offlineCost (A.conf []) σ + a

end KServer
