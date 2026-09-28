import Mathlib

namespace FatkhullinPolyak.Discrete

/-- A real square matrix `M` is **Hurwitz** if every complex eigenvalue of `M` has negative real
part (Fatkhullin–Polyak, p. 3: `ℜλᵢ(M) < 0` for all `i`). Eigenvalues are the elements of the
spectrum of `M` viewed as a complex matrix. -/
def IsHurwitz {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), z.re < 0

/-- The largest real part of a complex eigenvalue of `M`, i.e. `ℜλₙ(M)` in the paper's ordering
of eigenvalues by increasing real part (p. 2). The spectrum is finite, and nonempty when `n ≥ 1`. -/
noncomputable def maxRe {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (M.map (algebraMap ℝ ℂ)))

/-- The **stability degree** `σ(M) := −maxᵢ ℜλᵢ(M)` (Lemma A.5, p. 15). -/
noncomputable def stabDegree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  - maxRe M

/-- `λ₁(M)`: the smallest eigenvalue of a symmetric matrix `M` (the paper indexes eigenvalues in
increasing order, p. 2). Mathlib's `IsHermitian.eigenvalues` are unsorted, so this is their
minimum. Junk value `0` if `M` is not symmetric or `n = 0`. -/
noncomputable def lamMin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : M.IsHermitian then
    if hn : 0 < n then Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ h.eigenvalues else 0
  else 0

/-- `λₙ(M)`: the largest eigenvalue of a symmetric matrix `M`. Junk value `0` if `M` is not
symmetric or `n = 0`. -/
noncomputable def lamMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : M.IsHermitian then
    if hn : 0 < n then Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ h.eigenvalues else 0
  else 0

/-- The Frobenius norm `‖M‖_F = √(∑ᵢⱼ Mᵢⱼ²)`. -/
noncomputable def frobNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The Frobenius inner product `⟨M, N⟩ = Tr(MᵀN) = ∑ᵢⱼ Mᵢⱼ Nᵢⱼ`. -/
def frobInner {p q : ℕ} (M N : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * N i j

/-- The spectral norm `‖M‖` (largest singular value): the operator norm of `M` as a linear map
between Euclidean spaces (Mathlib's `Matrix.instL2OpNormedAddCommGroup`). -/
noncomputable def specNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  @Norm.norm _ (Matrix.instL2OpNormedAddCommGroup (m := Fin p) (n := Fin q) (𝕜 := ℝ)).toNorm M

open Classical in
/-- The solution of the Lyapunov equation `Mᵀ X + X M + W = 0`, when it is unique (which is the
case whenever `M` is Hurwitz); junk value `0` otherwise. -/
noncomputable def lyapSol {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : ∃! X : Matrix (Fin n) (Fin n) ℝ, M.transpose * X + X * M + W = 0 then h.choose else 0

end FatkhullinPolyak.Discrete
