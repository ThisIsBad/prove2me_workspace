import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- The bookkeeping of the multicut L-shaped algorithm (Birge–Louveaux 1988, §3,
pp. 386–387): the feasibility cuts `(D_l, d_l)` of (12) in the order generated, for each
scenario `k` its optimality cuts `(E_{l(k)}, e_{l(k)})` of (13) in the order generated
(so `t(k)` is the length of `optCuts k`), and the number `nOpt` of returns to Step 1 made
from Step 3 so far. -/
structure State (n1 K : ℕ) where
  feasCuts : List ((Fin n1 → ℝ) × ℝ)
  optCuts : Fin K → List ((Fin n1 → ℝ) × ℝ)
  nOpt : ℕ

/-- Step 0: `s = ν = 0` and `t_k = 0` for all `k` — no cuts, no returns yet. -/
def init : State n1 K := ⟨[], fun _ => [], 0⟩

/-- `(x, θ)` is an optimal solution of the master (11)–(13) built from the cuts of `s`
(the problem solved in Step 1). -/
def IsMasterOptimal (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (x : Fin n1 → ℝ)
    (θ : Fin K → ℝ) : Prop :=
  IsMultiOptimal inst s.feasCuts s.optCuts x θ

/-- Condition (14) for scenario `k` at the master solution `(x, θ)` with simplex
multiplier `π` of basis `b`: `θ_k < p_k π (h_k − T_k x)`. A scenario with no optimality
cut yet has `θ_k = −∞` (p. 386) and therefore always satisfies (14). -/
def Cond14 (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (x : Fin n1 → ℝ) (θ : Fin K → ℝ)
    (k : Fin K) (b : Basis n2 m2) : Prop :=
  s.optCuts k = [] ∨
    θ k < inst.p k * (multiplier inst b (inst.q k) ⬝ᵥ (inst.h k - inst.T k *ᵥ x))

open Classical in
/-- One major iteration of the multicut L-shaped algorithm (§3, pp. 386–387), from the
state at a Step 1 to the state at the next return to Step 1. Every choice the paper leaves
open (which optimal master solution, which optimal simplex basis) is allowed.

* `feas` — Step 1 yields an optimal `(x^ν, θ^ν)`; in Step 2 ("as before", p. 386) the
  scenarios are examined in the order `k = 1, …, K` and `k` is the first whose
  feasibility LP has optimal value `w¹ > 0`; with `σ^ν` the multiplier of a
  simplex-optimal basis of that LP, the feasibility cut `D_{s+1} = σ^ν T_k`,
  `d_{s+1} = σ^ν h_k` is appended, and the algorithm returns to Step 1.
* `opt` — Step 1 yields an optimal `(x^ν, θ^ν)`; every feasibility LP has value `w¹ = 0`;
  in Step 3, `β k` is a simplex-optimal basis of Problem `k` of type (7) at `x^ν`; for every
  `k` satisfying (14) the cut (15)–(16) is appended to scenario `k`'s list; at least one
  `k` satisfies (14) (otherwise the algorithm stops), and the algorithm returns to Step 1,
  incrementing `nOpt`. -/
inductive Step (inst : Instance n1 n2 m1 m2 K) : State n1 K → State n1 K → Prop
  | feas (s : State n1 K) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) (k : Fin K) (b : FeasBasis n2 m2)
      (hopt : IsMasterOptimal inst s x θ)
      (hfirst : ∀ k', k' < k → feasLPValue inst k' x = 0)
      (hpos : 0 < feasLPValue inst k x)
      (hb : IsFeasSimplexOptimal inst k b x) :
      Step inst s ⟨s.feasCuts ++ [feasCutCoeffs inst k b], s.optCuts, s.nOpt⟩
  | opt (s : State n1 K) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2)
      (hopt : IsMasterOptimal inst s x θ)
      (hfeas : ∀ k, feasLPValue inst k x = 0)
      (hβ : ∀ k, IsSimplexOptimal inst k (β k) x)
      (hS : ∃ k, Cond14 inst s x θ k (β k)) :
      Step inst s ⟨s.feasCuts,
        fun k => if Cond14 inst s x θ k (β k) then s.optCuts k ++ [optCut inst k (β k)]
          else s.optCuts k,
        s.nOpt + 1⟩

/-- `s` is reachable: some run of the multicut algorithm, started at Step 0, is at state
`s` when it returns to Step 1. -/
def Reachable (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) : Prop :=
  Relation.ReflTransGen (Step inst) init s

end MulticutLShaped.Bound
