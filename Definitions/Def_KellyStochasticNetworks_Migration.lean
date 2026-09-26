import Mathlib

namespace KellyStochasticNetworks

/-- `Tjk j k n` transfers one individual from colony `j` to colony `k`.
This is the operator `T^{jk}` of Kelly–Yudovina, *Stochastic Networks*, p. 26. -/
def Tjk {J : ℕ} (j k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else if i = k then n k + 1 else n i

/-- `Tout j n` is the operator `T^{j→}` of p. 30: an individual leaves the system from
colony `j`. -/
def Tout {J : ℕ} (j : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = j then n j - 1 else n i

/-- `Tin k n` is the operator `T^{→k}` of p. 30: an individual enters colony `k` from the
outside world. -/
def Tin {J : ℕ} (k : Fin J) (n : Fin J → ℕ) : Fin J → ℕ := fun i =>
  if i = k then n k + 1 else n i

/-- `phiProd φ j m` is the product `∏_{r=1}^{m} φ_j(r)` appearing in the product-form
distributions of Theorems 2.4 and 2.8; it is `1` when `m = 0`. -/
def phiProd {J : ℕ} (φ : Fin J → ℕ → ℝ) (j : Fin J) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 1 m, φ j r

/-- The transition rates of a **closed migration process** (p. 27): the only transitions are
`n ↦ T^{jk} n`, at rate `λ_{jk} φ_j(n_j)`.  The rate from a state to itself is zero because
`φ_j(0) = 0` is assumed wherever these rates are used. -/
noncomputable def closedMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (φ : Fin J → ℕ → ℝ) :
    (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  ∑ j, ∑ k, if m = Tjk j k n then lam j k * φ j (n j) else 0

/-- The transition rates of an **open migration process** (p. 30): transfers between colonies at
rate `λ_{jk} φ_j(n_j)`, departures from colony `j` at rate `μ_j φ_j(n_j)`, and Poisson
immigration into colony `k` at rate `ν_k`. -/
noncomputable def openMigrationRates {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (φ : Fin J → ℕ → ℝ) : (Fin J → ℕ) → (Fin J → ℕ) → ℝ := fun n m =>
  closedMigrationRates lam φ n m
    + (∑ j, if m = Tout j n then mu j * φ j (n j) else 0)
    + (∑ k, if m = Tin k n then nu k else 0)

/-- The **traffic equations** (2.1) of a closed migration process. -/
def ClosedTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (α : Fin J → ℝ) : Prop :=
  (∀ j, 0 < α j) ∧ (∑ j, α j = 1) ∧ ∀ j, α j * ∑ k, lam j k = ∑ k, α k * lam k j

/-- The **traffic equations** (2.2) of an open migration process. -/
def OpenTraffic {J : ℕ} (lam : Fin J → Fin J → ℝ) (mu nu α : Fin J → ℝ) : Prop :=
  ∀ j, α j * (mu j + ∑ k, lam j k) = nu j + ∑ k, α k * lam k j

/-- The single-colony marginal `π_j(m) = g_j⁻¹ α_j^m / ∏_{r=1}^m φ_j(r)` of Theorem 2.8. -/
noncomputable def migrationMarginal {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (j : Fin J) (m : ℕ) : ℝ := (g j)⁻¹ * (α j ^ m / phiProd φ j m)

/-- The product-form distribution `π(n) = ∏_j π_j(n_j)` of Theorem 2.8. -/
noncomputable def openMigrationPi {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (n : Fin J → ℕ) : ℝ := ∏ j, migrationMarginal α g φ j (n j)

/-- The transition rates of an M/M/1 queue with arrival rate `lam` and service rate `mu`
(p. 22): `q(j, j+1) = lam` and `q(j, j-1) = mu`. -/
noncomputable def mm1Rates (lam mu : ℝ) : ℕ → ℕ → ℝ := fun j k =>
  if k = j + 1 then lam else if j = k + 1 then mu else 0

/-- The number of customers in the system at time `s`, for `N` customers whose arrival and
departure times are `a i` and `d i`.  This is the function `n(·)` of section 2.5. -/
noncomputable def occupancy {N : ℕ} (a d : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ i, Set.indicator (Set.Ico (a i) (d i)) (fun _ => (1 : ℝ)) s

end KellyStochasticNetworks
