import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-! # The constructions of Theorem 5 (pp. 24–25) and Theorem 2(d) (p. 14) -/

/-- The number of machines `m = n(n − 1) + 2` of the construction of Theorem 5(a), p. 24. -/
def numMachines (n : ℕ) : ℕ := n * (n - 1) + 2

theorem numMachines_pos (n : ℕ) : 0 < numMachines n := by
  unfold numMachines; omega

/-- An admissible assignment `ι` of machines to ordered pairs of distinct jobs (p. 24): `ι j k`
is the (1-based) index of the machine `M_{ι(j,k)}` that corresponds to the pair `(J_j, J_k)`,
`j ≠ k` (values of `ι` on the diagonal are ignored). Admissible means
1. `ι` takes values in the middle machines `{2, …, m − 1} = {2, …, n(n−1)+1}`,
2. `ι` is injective on ordered pairs of distinct jobs,
3. every middle machine is `ι(j,k)` for some pair (so `ι` is a bijection onto them),
4. "for no `J_ℓ` some `M_{ι(j,ℓ)}` directly follows an `M_{ι(ℓ,k)}`": never
   `ι(j,ℓ) = ι(ℓ,k) + 1` (here `j = k` is allowed). -/
def Admissible (n : ℕ) (ι : Fin n → Fin n → ℕ) : Prop :=
  (∀ j k : Fin n, j ≠ k → 2 ≤ ι j k ∧ ι j k ≤ n * (n - 1) + 1) ∧
  (∀ j k j' k' : Fin n, j ≠ k → j' ≠ k' → ι j k = ι j' k' → j = j' ∧ k = k') ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ n * (n - 1) + 1 → ∃ j k : Fin n, j ≠ k ∧ ι j k = i) ∧
  (∀ j ℓ k : Fin n, j ≠ ℓ → ℓ ≠ k → ι j ℓ ≠ ι ℓ k + 1)

/-- The partial sums `q_{ℓ i}` of the construction (display on p. 24), in `ℤ`, for the graph
`adj`, the assignment `ι` and the parameters `λ`, `μ`; the cases are tested in the order printed:
`iμ + λ` if `i = ι(ℓ,k)` and `(ℓ,k) ∈ A`; `iμ + λ + 1` if `i = ι(ℓ,k)` and `(ℓ,k) ∉ A`;
`iμ − λ` if `i + 1 = ι(j,ℓ)` and `(j,ℓ) ∈ A`; `iμ − λ − 1` if `i + 1 = ι(j,ℓ)` and `(j,ℓ) ∉ A`;
`iμ` otherwise (always with `k ≠ ℓ`, `j ≠ ℓ`). -/
def partialSum {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)
    (ℓ : Fin n) (i : ℕ) : ℤ :=
  if ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k ∧ adj ℓ k = true then (i : ℤ) * mu + lam
  else if ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k ∧ adj ℓ k = false then (i : ℤ) * mu + lam + 1
  else if ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ ∧ adj j ℓ = true then (i : ℤ) * mu - lam
  else if ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ ∧ adj j ℓ = false then (i : ℤ) * mu - lam - 1
  else (i : ℤ) * mu

/-- The processing times of the construction, in `ℤ` (p. 25): `p_{ℓ1} = q_{ℓ1}` and
`p_{ℓi} = q_{ℓi} − q_{ℓ,i−1}` for `i = 2, …, m`. Machine `r : Fin m` is the paper's `M_{r+1}`. -/
def procTimeInt {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)
    (ℓ : Fin n) (r : Fin (numMachines n)) : ℤ :=
  if r.val = 0 then partialSum adj ι lam mu ℓ 1
  else partialSum adj ι lam mu ℓ (r.val + 1) - partialSum adj ι lam mu ℓ r.val

/-- The no-wait flow shop instance of Theorem 5 (p. 25): `n` jobs, `numMachines n` machines and
processing times `procTimeInt`, converted to `ℕ` with `Int.toNat`. Theorem 5's
milestone on positivity shows that every `procTimeInt` is `≥ 1` for admissible `ι`, `λ ≥ 1`,
`μ ≥ 2λ + 3`, so the conversion changes nothing there. -/
def procTimes {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ) :
    Fin n → Fin (numMachines n) → ℕ :=
  fun ℓ r => (procTimeInt adj ι lam mu ℓ r).toNat

/-- The graph `G = (V, A)` of Theorem 2(d), p. 14, built from `G' = (V', A')` on `Fin n` and a
chosen vertex `v'`: `V = V' ∪ {v''}` with `v''` the new last vertex `Fin.last n`, and
`A = {(u,v) | (u,v) ∈ A', v ≠ v'} ∪ {(u,v'') | (u,v') ∈ A'}`. No arc leaves `v''`. -/
def hcToHpGraph {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    Fin (n + 1) → Fin (n + 1) → Bool :=
  fun a b =>
    if ha : a = Fin.last n then false
    else if hb : b = Fin.last n then adj' (a.castPred ha) v'
    else adj' (a.castPred ha) (b.castPred hb) && decide (b.castPred hb ≠ v')

end SchedComplexity.NoWait
