import Mathlib
import Definitions.Def_KumarSeidman_CAF_Trajectory

namespace KumarSeidman.CAF

variable {P M : ℕ}

/-- The work that a part in buffer `b = b_{p,i}` still requires from machine `m = μ_{p,i}`
before it moves to another machine or leaves the system:
`τ_{p,i} + τ_{p,i+1} + ⋯ + τ_{p,i+η_{p,i}-1}`, where
`η_{p,i} = max {j : μ_{p,k} = m for i ≤ k ≤ i + j − 1}` (p. 294); the sum runs over the
maximal block of consecutive stages `k ≥ i` of route `p` that are all at `m`, and stops at the
end of the route. -/
noncomputable def System.workAhead (S : System P M) (b : Buffer S) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (S.n b.1) =>
      b.2 ≤ k ∧ ∀ l : Fin (S.n b.1), b.2 ≤ l → l ≤ k → S.μ b.1 l = S.mach b),
    S.τ b.1 k

/-- The Lyapunov function (15) of machine `m` (p. 294):
`V_m(t) = Σ_{(p,i): μ_{p,i} = m} x_{p,i}(t) [τ_{p,i} + ⋯ + τ_{p,i+η_{p,i}-1}]`. -/
noncomputable def Trajectory.V {S : System P M} (T : Trajectory S) (m : Fin M) (t : ℝ) : ℝ :=
  ∑ b ∈ S.B m, T.x b t * S.workAhead b

/-- `δ̄_m = max_{b, b' ∈ B_m} δ_{b,b'}` (p. 295, after (18)), the largest set-up time between
two distinct buffers of machine `m`; it is `0` if `B_m` has fewer than two buffers. -/
noncomputable def System.deltaBar (S : System P M) (m : Fin M) : ℝ :=
  ((S.B m ×ˢ S.B m).filter (fun q => q.1 ≠ q.2)).fold max 0 (fun q => S.δ q.1 q.2)

/-- `τ̄_m = max_{(p,i): μ_{p,i} = m} [τ_{p,i} + ⋯ + τ_{p,i+η_{p,i}-1}]` (p. 295, after (22)),
for a machine with `B_m ≠ ∅`. -/
noncomputable def System.tauBar (S : System P M) (m : Fin M) (hB : (S.B m).Nonempty) : ℝ :=
  (S.B m).sup' hB S.workAhead

/-- `τ̲_m = min_{(p,i): μ_{p,i} = m} τ_{p,i}` (p. 295, after (22)), for `B_m ≠ ∅`. -/
noncomputable def System.tauLow (S : System P M) (m : Fin M) (hB : (S.B m).Nonempty) : ℝ :=
  (S.B m).inf' hB S.tau

/-- `Γ_m = max (2 δ̄ τ̄ / (ε_m τ̲ (1 − ρ'_m)) + K_m τ̄ / ε_m, δ̄)` (p. 295). -/
noncomputable def System.Gamma (S : System P M) (m : Fin M) (hB : (S.B m).Nonempty)
    (ε K : Fin M → ℝ) : ℝ :=
  max (2 * S.deltaBar m * S.tauBar m hB / (ε m * S.tauLow m hB * (1 - S.rhoPrime m))
      + K m * S.tauBar m hB / ε m) (S.deltaBar m)

/-- The class of machine `m` (under `↔`) is a minimal element of the partial order `→`
on classes (p. 294): every machine from which `m` is reachable is reachable from `m`. -/
def System.IsMinimal (S : System P M) (m : Fin M) : Prop :=
  ∀ m' : Fin M, S.Reach m' m → S.Reach m m'

/-- A set `U` of machines is closed upstream: if `(m', m'') ∈ A` and `m'' ∈ U` then `m' ∈ U`.
The union of the classes removed in the induction of the proof of Theorem 1 (p. 295) is such a
set. -/
def System.UpstreamClosed (S : System P M) (U : Finset (Fin M)) : Prop :=
  ∀ m' m'' : Fin M, S.Arc m' m'' → m'' ∈ U → m' ∈ U

/-- Buffer `b_{p,i}` is the head of a block of visits to its machine: `i = 1`, or
`μ_{p,i-1} ≠ μ_{p,i}` (the summation range `μ_{p,i} = m, μ_{p,i−1} ≠ m` of (16)). -/
def System.IsHead (S : System P M) (b : Buffer S) : Prop :=
  ∀ b' : Buffer S, S.prev b = some b' → S.mach b' ≠ S.mach b

open Classical in
/-- `Γ̄ = Σ_{(p,i): μ_{p,i} = m, μ_{p,i−1} ≠ m} Γ [τ_{p,i} + ⋯ + τ_{p,i+η_{p,i}−1}]`
(p. 295, after (23)). -/
noncomputable def System.GammaBar (S : System P M) (m : Fin M) (Γ : ℝ) : ℝ :=
  ∑ b ∈ (S.B m).filter (fun b => S.IsHead b), Γ * S.workAhead b

end KumarSeidman.CAF
