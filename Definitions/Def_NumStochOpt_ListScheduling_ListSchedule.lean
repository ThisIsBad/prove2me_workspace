import Mathlib

namespace NumStochOpt.ListScheduling

/-- The first available machine given the current machine loads `ℓ`: a machine of least
current load, ties broken towards the lowest index (`none` only when `m = 0`). With
nonnegative processing times and no idle time, machine `i` becomes free at time `ℓ i`. -/
noncomputable def firstAvailable {m : ℕ} (ℓ : Fin m → ℝ) : Option (Fin m) :=
  if h : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty then
    some ((Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).min' h)
  else none

/-- Machine loads after list scheduling the jobs `0, …, k-1` in index order on `m` machines:
each next job on the list is assigned to the first available machine. -/
noncomputable def lsLoads (m : ℕ) (p : ℕ → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun i =>
      if firstAvailable (lsLoads m p k) = some i then lsLoads m p k i + p k
      else lsLoads m p k i

/-- The list-scheduling makespan `C^H_n(m)`: the maximum machine load after list scheduling
the first `n` jobs (in the fixed order `0, 1, …, n-1`) on `m` machines. -/
noncomputable def listMakespan (n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨆ i : Fin m, lsLoads m p n i

end NumStochOpt.ListScheduling
