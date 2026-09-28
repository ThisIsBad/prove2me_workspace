import Mathlib

namespace DSSYKScales

open Filter Topology

/-- The double-scaled limit of SYK (Susskind 2022, eq. (3.3)): a sequence of models
indexed by `n`, with `N n` fermions and interaction order `q n`, such that `N n → ∞`
and `(q n)^2 / N n → lam`, where the fixed parameter `lam` is strictly positive. -/
def IsDoubleScaledLimit (N q : ℕ → ℕ) (lam : ℝ) : Prop :=
  0 < lam ∧
  Tendsto (fun n => (N n : ℝ)) atTop atTop ∧
  Tendsto (fun n => ((q n : ℝ) ^ 2) / (N n : ℝ)) atTop (𝓝 lam)

/-- The "epidemic" scrambling probability of DSSYK∞ as a function of cosmic time `t`
(Susskind 2022, eq. (8.1)):
`P(t) = 1 - (1 + (q/N) * exp((q - 1) J t)) ^ (-1/(q - 1))`. -/
noncomputable def scramblingProbability (N q : ℕ) (J t : ℝ) : ℝ :=
  1 - (1 + (q : ℝ) / (N : ℝ) * Real.exp (((q : ℝ) - 1) * J * t)) ^ (-1 / ((q : ℝ) - 1))

/-- Infinite-temperature second moment `⟨H_c^2⟩` of the cosmic Hamiltonian (3.4):
the number `C(N, q)` of `q`-fold couplings times the coupling variance
`⟨j j⟩ = q! J^2 / N^(q-1)` (Susskind 2022, eqs. (3.4), (3.9), (11.1)). -/
noncomputable def cosmicHamiltonianSecondMoment (N q : ℕ) (J : ℝ) : ℝ :=
  (N.choose q : ℝ) * ((q.factorial : ℝ) / (N : ℝ) ^ (q - 1) * J ^ 2)

/-- Infinite-temperature second moment `⟨H_s^2⟩` of the string-unit Hamiltonian
`H_s = H_c / q` (Susskind 2022, eqs. (3.7), (11.2)). -/
noncomputable def stringHamiltonianSecondMoment (N q : ℕ) (J : ℝ) : ℝ :=
  cosmicHamiltonianSecondMoment N q J / (q : ℝ) ^ 2

end DSSYKScales
