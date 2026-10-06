import Mathlib

namespace MulticlassQNet.FirstOrder

/-- Open multiclass queueing network data (Bertsimas–Paschalidis–Tsitsiklis 1992, §2, p. 6):
`N` single-server stations and `R` job classes. Class `r` is served at station `σ r`; after
service a class-`r` job becomes a class-`s` job with probability `p r s`, or exits with
probability `1 - ∑ s, p r s`; class-`r` jobs arrive from outside as a Poisson stream of rate
`lam0 r`; class-`r` service times are exponential with rate `μ r`. -/
structure Network (N R : ℕ) where
  /-- station of each class, the paper's `σ(r)` -/
  σ : Fin R → Fin N
  /-- routing probabilities `p_{rs}` -/
  p : Fin R → Fin R → ℝ
  /-- external arrival rates `λ_{0r}` -/
  lam0 : Fin R → ℝ
  /-- service rates `μ_r` -/
  μ : Fin R → ℝ
  p_nonneg : ∀ r s, 0 ≤ p r s
  p_row_sum_le_one : ∀ r, ∑ s, p r s ≤ 1
  lam0_nonneg : ∀ r, 0 ≤ lam0 r
  μ_pos : ∀ r, 0 < μ r

namespace Network

variable {N R : ℕ} (net : Network N R)

/-- The exit probability `p_{r0} = 1 - ∑_s p_{rs}`. -/
def exitProb (r : Fin R) : ℝ := 1 - ∑ s, net.p r s

/-- `C_i`, the set of classes served at station `i`. -/
def C (i : Fin N) : Finset (Fin R) := Finset.univ.filter (fun r => net.σ r = i)

/-- `lam` solves the traffic equations (15):
`λ_r = λ_{0r} + ∑_{r'} λ_{r'} p_{r'r}` for every class `r`. -/
def IsTrafficSolution (lam : Fin R → ℝ) : Prop :=
  ∀ r, lam r = net.lam0 r + ∑ r', lam r' * net.p r' r

/-- The network is open: the homogeneous traffic system `v_r = ∑_{r'} v_{r'} p_{r'r}` has only
the zero solution (equivalently `I - Pᵀ` is invertible), so (15) has a unique solution. -/
def IsOpen : Prop :=
  ∀ v : Fin R → ℝ, (∀ r, v r = ∑ r', v r' * net.p r' r) → v = 0

/-- The load condition of §4.1 (p. 13): `∑_{r ∈ C_i} λ_r / μ_r < 1` at every station `i`. -/
def LoadLtOne (lam : Fin R → ℝ) : Prop :=
  ∀ i, ∑ r ∈ net.C i, lam r / net.μ r < 1

end Network

end MulticlassQNet.FirstOrder
