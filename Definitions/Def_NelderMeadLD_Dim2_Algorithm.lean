import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

namespace NelderMeadLD.Dim2

/-- Euclidean `n`-space `ℝⁿ` with the two-norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordering (2.3), p. 115: `f(x₁) ≤ f(x₂) ≤ ⋯ ≤ f(x_{n+1})`.
Index `i : Fin (n+1)` (0-based) is the paper's vertex `x_{i+1}`. -/
def Sorted {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) : Prop :=
  ∀ i j : Fin (n + 1), i ≤ j → f (x i) ≤ f (x j)

/-- The next-worst vertex `x_n` of the paper, 0-based index `n - 1`. -/
def nextWorst (n : ℕ) : Fin (n + 1) := ⟨n - 1, by omega⟩

/-- The centroid `x̄ = ∑_{i=1}^n x_i / n` of the `n` best vertices (p. 116). -/
noncomputable def centroid {n : ℕ} (x : Fin (n + 1) → E n) : E n :=
  (1 / (n : ℝ)) • ∑ i : Fin n, x i.castSucc

/-- The trial point (2.12), p. 118: `z(τ) = (1 + τ) x̄ - τ x_{n+1}`. -/
noncomputable def trial {n : ℕ} (x : Fin (n + 1) → E n) (τ : ℝ) : E n :=
  (1 + τ) • centroid x - τ • x (Fin.last n)

/-- Steps 2–5 of one iteration of Algorithm NM (pp. 115–116), applied to an ordered simplex `x`.
`fr = f(x_r)` with `x_r = z(ρ)`, `x_e = z(ρχ)`, `x_c = z(ργ)`, `x_cc = z(-γ)`.
* Reflect: if `f₁ ≤ f_r < f_n`, accept `x_r`.
* Expand: if `f_r < f₁`, accept `x_e` if `f_e < f_r`, otherwise accept `x_r`.
* Outside contraction: if `f_n ≤ f_r < f_{n+1}`, accept `x_c` if `f_c ≤ f_r`, otherwise shrink.
* Inside contraction: if `f_r ≥ f_{n+1}`, accept `x_cc` if `f_cc < f_{n+1}`, otherwise shrink. -/
noncomputable def move {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (x : Fin (n + 1) → E n) : NelderMeadLD.Conv1D.Move :=
  let fr := f (trial x ρ)
  let f1 := f (x 0)
  let fn := f (x (nextWorst n))
  let fw := f (x (Fin.last n))
  if f1 ≤ fr ∧ fr < fn then NelderMeadLD.Conv1D.Move.reflect
  else if fr < f1 then (if f (trial x (ρ * χ)) < fr then NelderMeadLD.Conv1D.Move.expand else NelderMeadLD.Conv1D.Move.reflect)
  else if fr < fw then (if f (trial x (ρ * γ)) ≤ fr then NelderMeadLD.Conv1D.Move.outside else NelderMeadLD.Conv1D.Move.shrink)
  else (if f (trial x (-γ)) < fw then NelderMeadLD.Conv1D.Move.inside else NelderMeadLD.Conv1D.Move.shrink)

/-- The coefficient τ (2.13) of the accepted point: ρ (reflection), ρχ (expansion),
ργ (outside contraction), -γ (inside contraction). The value on `shrink` is unused. -/
def tau (ρ χ γ : ℝ) : NelderMeadLD.Conv1D.Move → ℝ
  | NelderMeadLD.Conv1D.Move.reflect => ρ
  | NelderMeadLD.Conv1D.Move.expand => ρ * χ
  | NelderMeadLD.Conv1D.Move.outside => ρ * γ
  | NelderMeadLD.Conv1D.Move.inside => -γ
  | NelderMeadLD.Conv1D.Move.shrink => 0

/-- Insertion position of the accepted point `v` (nonshrink ordering rule, p. 116, read with
`min`): the number of retained vertices `x₁, …, x_n` with `f(x_i) ≤ f(v)`. -/
noncomputable def insertPos {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f (x i.castSucc) ≤ f v)).card

/-- The nonshrink ordering rule (p. 116): the worst vertex `x_{n+1}` is discarded, the accepted
point `v` is placed after every retained vertex whose value is `≤ f(v)` (0-based position
`insertPos f x v`), and the retained vertices keep their relative order. -/
noncomputable def insertVertex {n : ℕ} (f : E n → ℝ) (x : Fin (n + 1) → E n) (v : E n) :
    Fin (n + 1) → E n := fun i =>
  if i.val < insertPos f x v then x i
  else if i.val = insertPos f x v then v
  else x ⟨i.val - 1, by omega⟩

/-- The shrink points of step 5: `v_i = x₁ + σ (x_i - x₁)` (for `i = 0` this is `x₁` itself). -/
noncomputable def shrinkPoints {n : ℕ} (σ : ℝ) (x : Fin (n + 1) → E n) : Fin (n + 1) → E n :=
  fun i => x 0 + σ • (x i - x 0)

/-- The shrink ordering rule (pp. 116–117): `y` lists `x₁, v₂, …, v_{n+1}` in some order satisfying
(2.3); if `min_i f(v_i) = f(x₁)` (equivalently, no new point is better than `x₁`), then `y₁ = x₁`.
Any other ordering is allowed ("whatever rule"). -/
def IsShrinkSuccessor {n : ℕ} (f : E n → ℝ) (σ : ℝ) (x y : Fin (n + 1) → E n) : Prop :=
  (∃ π : Equiv.Perm (Fin (n + 1)), y = shrinkPoints σ x ∘ π) ∧ Sorted f y ∧
    ((∀ i, f (x 0) ≤ f (shrinkPoints σ x i)) → y 0 = x 0)

/-- One iteration of Algorithm NM from the ordered simplex `x` to the ordered simplex `y`. -/
def IsNMStep {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (x y : Fin (n + 1) → E n) : Prop :=
  (move f ρ χ γ x = NelderMeadLD.Conv1D.Move.shrink → IsShrinkSuccessor f σ x y) ∧
    (move f ρ χ γ x ≠ NelderMeadLD.Conv1D.Move.shrink → y = insertVertex f x (trial x (tau ρ χ γ (move f ρ χ γ x))))

/-- A run of Algorithm NM: an ordered initial simplex `Δ 0` and successive iterations. It is a
relation because the paper leaves the ordering after a shrink partly open. -/
def IsNMRun {n : ℕ} (f : E n → ℝ) (ρ χ γ σ : ℝ) (Δ : ℕ → Fin (n + 1) → E n) : Prop :=
  Sorted f (Δ 0) ∧ ∀ k, IsNMStep f ρ χ γ σ (Δ k) (Δ (k + 1))

/-- Iteration `k` of the run `Δ` is a shrink step. -/
def IsShrinkAt {n : ℕ} (f : E n → ℝ) (ρ χ γ : ℝ) (Δ : ℕ → Fin (n + 1) → E n) (k : ℕ) : Prop :=
  move f ρ χ γ (Δ k) = NelderMeadLD.Conv1D.Move.shrink

/-- The edge matrix (2.10), p. 118: column `j` is `x_j - x_{n+1}`, `j = 1, …, n`. -/
noncomputable def edgeMatrix {n : ℕ} (x : Fin (n + 1) → E n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun r c => x c.castSucc r - x (Fin.last n) r

/-- A simplex is nondegenerate if its edge matrix is nonsingular (p. 118). -/
def Nondegenerate {n : ℕ} (x : Fin (n + 1) → E n) : Prop :=
  (edgeMatrix x).det ≠ 0

/-- The volume (2.11), p. 118: `vol(Δ) = |det M| / n!`. -/
noncomputable def vol {n : ℕ} (x : Fin (n + 1) → E n) : ℝ :=
  |(edgeMatrix x).det| / (n.factorial : ℝ)

/-- The diameter (p. 118): `diam(Δ) = max_{i ≠ j} ‖x_i - x_j‖` (two-norm), computed as a finite
maximum over all pairs (the pairs `i = j` contribute `0`). -/
noncomputable def diam {n : ℕ} (x : Fin (n + 1) → E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin (n + 1) × Fin (n + 1) => ‖x ij.1 - x ij.2‖)

end NelderMeadLD.Dim2
