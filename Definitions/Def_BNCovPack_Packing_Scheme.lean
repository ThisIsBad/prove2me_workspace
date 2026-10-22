import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- The state of the online fractional packing scheme (Buchbinder–Naor 2009, §3, p. 5): the
current primal (covering) solution `x : I → ℝ` and the current dual (packing) solution
`y : Fin m → ℝ`, one dual variable per column (round). -/
structure State (I : Type*) (m : ℕ) where
  /-- the primal variables `x(i)` -/
  x : I → ℝ
  /-- the dual variables `y(k)` -/
  y : Fin m → ℝ

/-- The initial state (p. 4): every `x(i)` and every `y(k)` is zero. -/
def initState (I : Type*) (m : ℕ) : State I m where
  x := fun _ => 0
  y := fun _ => 0

/-- Line (i) of the scheme (p. 5): the prefix maximum `aᵢ(max) = max_{k=1}^{j} a(i,k)` used in
round `j`, i.e. the largest coefficient of `x(i)` among the columns revealed so far
(`k ≤ j`, column `j` included). -/
noncomputable def prefixMax {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (i : I) (j : Fin m) : ℝ :=
  (Finset.univ.filter (fun k : Fin m => k ≤ j)).sup'
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_refl j⟩⟩ (inst.a i)

/-- The increment function of line (ii)b (p. 5) in round `j`, evaluated at the dual vector `y`:
`(1/(n aᵢ(max))) [exp((B/(2c(i))) ∑_{k=1}^{j} a(i,k) y(k)) − 1]`, where `n = |I|` is the number
of primal variables and `aᵢ(max)` is the prefix maximum `prefixMax inst i j`. (If
`prefixMax inst i j = 0` then `1/0 = 0` in Lean; in that case every `a(i,k)`, `k ≤ j`, is zero
and the bracket is `0` as well.) -/
noncomputable def increment {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (y : Fin m → ℝ) (j : Fin m) (i : I) : ℝ :=
  1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
    (Real.exp (B / (2 * inst.c i) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k) - 1)

/-- The primal solution of round `j` when the new dual variable has been raised to `y(j) = t`
(line (ii)b, p. 5): `x(i) ← max{x(i), increment}`, with the dual vector `s.y` updated at
coordinate `j` to `t`. -/
noncomputable def primalAt {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) (t : ℝ) : I → ℝ :=
  fun i => max (s.x i) (increment inst B (Function.update s.y j t) j i)

/-- The value given to the new dual variable `y(j)` in round `j` (p. 4–5, discrete
implementation): "one should find the minimal `y(j)` such that the new primal constraint is
satisfied", i.e. the least `t ≥ 0` with `∑ᵢ a(i,j) x_t(i) ≥ 1`, where `x_t = primalAt … t`.
When the instance's column `j` has a positive entry this set is nonempty and closed, so the
infimum is attained; every theorem about the scheme carries that hypothesis. -/
noncomputable def roundValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ ∑ i, inst.a i j * primalAt inst B s j t i}

/-- Round `j` of the scheme (p. 5), applied to the state `s` reached after the earlier rounds:
line (i) sets `y(j) ← 0`; if the new primal constraint `∑ᵢ a(i,j) x(i) ≥ 1` already holds, the
while-loop (ii) does not run and nothing changes; otherwise `y(j)` is raised to the minimal
value `roundValue` at which the constraint holds, and every `x(i)` is updated by line (ii)b. -/
noncomputable def runRound {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (s : State I m) (j : Fin m) : State I m :=
  if 1 ≤ ∑ i, inst.a i j * s.x i then
    ⟨s.x, Function.update s.y j 0⟩
  else
    ⟨primalAt inst B s j (roundValue inst B s j),
      Function.update s.y j (roundValue inst B s j)⟩

/-- The state of the scheme after the first `r` rounds (the columns `k : Fin m` with `k < r`, in index
order), starting from `initState`. For `r ≥ m` it is the final state. -/
noncomputable def stateAfter {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) : ℕ → State I m
  | 0 => initState I m
  | r + 1 =>
    if h : r < m then runRound inst B (stateAfter inst B r) ⟨r, h⟩
    else stateAfter inst B r

/-- The value `X` of the primal (covering) solution after `r` rounds: `∑ᵢ c(i) x(i)`. -/
noncomputable def primalValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (r : ℕ) : ℝ :=
  ∑ i, inst.c i * (stateAfter inst B r).x i

/-- The value `Y` of the dual (packing) solution after `r` rounds: `∑_{k < r} y(k)` (the
objective coefficient of every `y(k)` is normalized to `1`, footnote 2, p. 4). -/
noncomputable def dualValue {I : Type*} [Fintype I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r), (stateAfter inst B r).y k

end BNCovPack.Packing
