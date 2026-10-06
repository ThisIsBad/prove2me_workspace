import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus

/-- The domain `D` of the variational problem (p. 166): matrices `ξ = (ξ_ij)` with
(4) `ξ_ij ≥ 0` for all `i, j` and (5) `∑_{i=1}^m ξ_ij = 1` for all `j` (column sums). -/
def D (m n : ℕ) : Set (Fin m → Fin n → ℝ) :=
  {ξ | (∀ i j, 0 ≤ ξ i j) ∧ ∀ j, ∑ i, ξ i j = 1}

namespace Market

variable {m n : ℕ}

/-- The function `φ(ξ) = ∑_i b_i log ∑_j p_ij ξ_ij` (p. 166), real-valued; at points with some
inner sum zero the paper's value is `−∞`, which `IsPhiMaximizer` accounts for. -/
noncomputable def phi (M : Market m n) (ξ : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, M.b i * Real.log (∑ j, M.P i j * ξ i j)

/-- `ξ` maximizes `φ` on `D` with the paper's convention `log 0 = −∞` (p. 167): `ξ ∈ D`, every
inner sum `∑_j p_ij ξ_ij` is positive, and `φ(η) ≤ φ(ξ)` for every `η ∈ D` whose inner sums are all
positive (the points of `D` with a zero inner sum have `φ = −∞` and are never larger). -/
def IsPhiMaximizer (M : Market m n) (ξ : Fin m → Fin n → ℝ) : Prop :=
  ξ ∈ D m n ∧ (∀ i, 0 < ∑ j, M.P i j * ξ i j) ∧
  ∀ η ∈ D m n, (∀ i, 0 < ∑ j, M.P i j * η i j) → M.phi η ≤ M.phi ξ

/-- The track probabilities (6) (p. 167): `π_j = max_i b_i p_ij / ∑_s p_is ξ_is`, the maximum
over the nonempty finite set of bettors taken as `Finset.sup'`. -/
noncomputable def trackProb (M : Market m n) (ξ : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' M.univ_nonempty (fun i => M.b i * M.P i j / ∑ s, M.P i s * ξ i s)

/-- The bets (7) (p. 167): `β_ij = ξ_ij π_j` with `π_j` from (6). -/
noncomputable def bets (M : Market m n) (ξ : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  ξ i j * M.trackProb ξ j

end Market

end PariMutuel.Consensus
