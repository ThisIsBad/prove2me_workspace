import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace MulticutLShaped.Bound

open StochasticProg.Recourse
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- `(x, θ_1, …, θ_K)` is feasible in the multicut master program (11)–(13)
(Birge–Louveaux 1988, p. 386) with feasibility cuts `F = [(D_1, d_1), …, (D_s, d_s)]` and,
for each scenario `k`, optimality cuts `C k = [(E_{1(k)}, e_{1(k)}), …]`:
`A x = b`, `x ≥ 0`, `D_l x ≥ d_l` for all `l` (12), and `E_{l(k)} x + θ_k ≥ e_{l(k)}` for all
`k` and `l(k)` (13). A `θ_k` whose scenario has no cut is unconstrained. -/
def MultiFeasible (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (C : Fin K → List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : Prop :=
  x ∈ K1 inst ∧ (∀ c ∈ F, c.2 ≤ c.1 ⬝ᵥ x) ∧ (∀ k, ∀ c ∈ C k, c.2 ≤ c.1 ⬝ᵥ x + θ k)

open Classical in
/-- The multicut master objective (11), `z = c x + Σ_k θ_k`, where — as on p. 386 — a `θ_k`
for which no constraint (13) is present is "set equal to −∞ and ignored in the
computation": the sum runs only over the scenarios `k` with at least one cut. -/
noncomputable def multiObj (inst : Instance n1 n2 m1 m2 K) (C : Fin K → List ((Fin n1 → ℝ) × ℝ))
    (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : ℝ :=
  inst.c ⬝ᵥ x + ∑ k ∈ Finset.univ.filter (fun k => C k ≠ []), θ k

/-- `(x, θ)` is an optimal solution of the multicut master (11)–(13): it is feasible and
its objective (11) is no larger than that of any feasible point. -/
def IsMultiOptimal (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (C : Fin K → List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : Prop :=
  MultiFeasible inst F C x θ ∧
    ∀ x' θ', MultiFeasible inst F C x' θ' → multiObj inst C x θ ≤ multiObj inst C x' θ'

/-- `(x, θ)` is feasible in the single-cut L-shaped master (4)–(6) (p. 386) with
feasibility cuts `F` and optimality cuts `L = [(E_1, e_1), …, (E_t, e_t)]`:
`A x = b`, `x ≥ 0`, `D_l x ≥ d_l` (5) and `E_l x + θ ≥ e_l` (6). -/
def LFeasible (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  x ∈ K1 inst ∧ (∀ c ∈ F, c.2 ≤ c.1 ⬝ᵥ x) ∧ (∀ c ∈ L, c.2 ≤ c.1 ⬝ᵥ x + θ)

open Classical in
/-- The L-shaped master objective (4), `z = c x + θ`; when no constraint (6) is present,
`θ` is ignored (p. 386) and the objective is `c x`. -/
noncomputable def LObj (inst : Instance n1 n2 m1 m2 K) (L : List ((Fin n1 → ℝ) × ℝ))
    (x : Fin n1 → ℝ) (θ : ℝ) : ℝ :=
  if L = [] then inst.c ⬝ᵥ x else inst.c ⬝ᵥ x + θ

/-- `(x, θ)` is an optimal solution of the L-shaped master (4)–(6). -/
def IsLOptimal (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  LFeasible inst F L x θ ∧
    ∀ x' θ', LFeasible inst F L x' θ' → LObj inst L x θ ≤ LObj inst L x' θ'

end MulticutLShaped.Bound
