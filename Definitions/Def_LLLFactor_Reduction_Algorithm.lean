import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.Reduction
noncomputable section

/-- A state of the algorithm (1.15): the current vectors `b₁, …, bₙ` (Lean index `i` is the
paper's `b_{i+1}`) and the current subscript `k`, stored as **the paper's** subscript. -/
abbrev State (n : ℕ) := (Fin n → LLLFactor.RedBasis.Vec n) × ℕ

/-- `r` is an integer nearest to `x`. Both nearest integers are allowed at a tie. -/
def IsNearestInt (r : ℤ) (x : ℝ) : Prop :=
  |x - (r : ℝ)| ≤ 1 / 2

/-- Replace `b_κ` by `b_κ − r b_l` (Lean indices), all other vectors unchanged. -/
def reduceBy {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (κ l : Fin n) (r : ℤ) : Fin n → LLLFactor.RedBasis.Vec n :=
  Function.update b κ (b κ - (r : ℝ) • b l)

/-- Condition (1.19) at the paper's subscript `k` (`2 ≤ k ≤ n`):
`|b_k^* + μ_{k,k−1} b_{k−1}^*|² < ¾ |b_{k−1}^*|²`. False outside `2 ≤ k ≤ n`. -/
def Cond119 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  ∃ h : 2 ≤ k ∧ k ≤ n,
    ‖LLLFactor.RedBasis.gs b ⟨k - 1, by omega⟩ + LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ • LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2
      < (3 / 4 : ℝ) * ‖LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2

/-- Condition (1.20) (equivalently (1.17) at `i = k`) at the paper's subscript `k`
(`2 ≤ k ≤ n`): `|b_k^* + μ_{k,k−1} b_{k−1}^*|² ≥ ¾ |b_{k−1}^*|²`. False outside `2 ≤ k ≤ n`. -/
def Cond120 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  ∃ h : 2 ≤ k ∧ k ≤ n,
    (3 / 4 : ℝ) * ‖LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2 ≤
      ‖LLLFactor.RedBasis.gs b ⟨k - 1, by omega⟩ + LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ • LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2

/-- Achieving (1.18) at the paper's subscript `k`: if `k > 1` (and `k ≤ n`) and
`|μ_{k,k−1}| > ½`, replace `b_k` by `b_k − r b_{k−1}` with `r` an integer nearest to
`μ_{k,k−1}`; otherwise nothing changes. -/
def Achieve118 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) (b' : Fin n → LLLFactor.RedBasis.Vec n) : Prop :=
  if h : 2 ≤ k ∧ k ≤ n then
    (|LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2 ∧ b' = b) ∨
    (1 / 2 < |LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ∧
      ∃ r : ℤ, IsNearestInt r (LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩) ∧
        b' = reduceBy b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ r)
  else b' = b

/-- One pass of the loop of case 2 for the vector with Lean index `κ` (the paper's `b_k`,
`κ = k − 1`): `l` is the largest index `< κ` with `|μ_{κ l}| > ½`, `r` an integer nearest to
`μ_{κ l}`, and `b_κ` is replaced by `b_κ − r b_l`. -/
def LoopStep {n : ℕ} (κ : Fin n) (c c' : Fin n → LLLFactor.RedBasis.Vec n) : Prop :=
  ∃ l : Fin n, l < κ ∧ 1 / 2 < |LLLFactor.RedBasis.mu c κ l| ∧
    (∀ l' : Fin n, l < l' → l' < κ → |LLLFactor.RedBasis.mu c κ l'| ≤ 1 / 2) ∧
    ∃ r : ℤ, IsNearestInt r (LLLFactor.RedBasis.mu c κ l) ∧ c' = reduceBy c κ l r

/-- Case 1 of (1.15), from state `s = (b, k)` to `s'`: `2 ≤ k ≤ n`; achieve (1.18); (1.19)
holds; interchange `b_{k−1}` and `b_k`; replace `k` by `k − 1`. -/
def Case1 {n : ℕ} (s s' : State n) : Prop :=
  ∃ h : 2 ≤ s.2 ∧ s.2 ≤ n, ∃ b' : Fin n → LLLFactor.RedBasis.Vec n,
    Achieve118 s.1 s.2 b' ∧ Cond119 b' s.2 ∧
    s'.1 = b' ∘ Equiv.swap (⟨s.2 - 2, by omega⟩ : Fin n) ⟨s.2 - 1, by omega⟩ ∧
    s'.2 = s.2 - 1

/-- Case 2 of (1.15), from state `s = (b, k)` to `s'`: `1 ≤ k ≤ n`; achieve (1.18);
`k = 1` or (1.20) holds; run the loop of case 2 until (1.21) holds; replace `k` by `k + 1`. -/
def Case2 {n : ℕ} (s s' : State n) : Prop :=
  ∃ h : 1 ≤ s.2 ∧ s.2 ≤ n, ∃ b' : Fin n → LLLFactor.RedBasis.Vec n,
    Achieve118 s.1 s.2 b' ∧ (s.2 = 1 ∨ Cond120 b' s.2) ∧
    Relation.ReflTransGen (LoopStep (⟨s.2 - 1, by omega⟩ : Fin n)) b' s'.1 ∧
    (∀ j : Fin n, (j : ℕ) < s.2 - 1 → |LLLFactor.RedBasis.mu s'.1 ⟨s.2 - 1, by omega⟩ j| ≤ 1 / 2) ∧
    s'.2 = s.2 + 1

/-- One step of the algorithm (1.15), from a situation (1.16)–(1.17) to the next. -/
def Step {n : ℕ} (s s' : State n) : Prop :=
  Case1 s s' ∨ Case2 s s'

/-- `s` is reachable by the algorithm started on the basis `b` (with `k = 2`). -/
def Reachable {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (s : State n) : Prop :=
  Relation.ReflTransGen Step (b, 2) s

/-- The situation (1.16)–(1.17) at the paper's subscript `k`:
(1.16) `|μ_{ij}| ≤ ½` for `1 ≤ j < i < k` (Lean: `j < i`, `i + 1 < k`);
(1.17) `|b_i^* + μ_{i,i−1} b_{i−1}^*|² ≥ ¾ |b_{i−1}^*|²` for `1 < i < k` (paper `i`, `i ≤ n`). -/
def Situation {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  (∀ i j : Fin n, j < i → (i : ℕ) + 1 < k → |LLLFactor.RedBasis.mu b i j| ≤ 1 / 2) ∧
  (∀ i : ℕ, 2 ≤ i → i < k → i ≤ n → Cond120 b i)

/-- `d_i = det((b_j, b_l))_{1 ≤ j,l ≤ i}` of (1.24), for `0 ≤ i ≤ n` (`d₀ = 1`, the empty
determinant); set to `0` for `i > n`, where the paper does not define it. -/
def gram {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (i : ℕ) : ℝ :=
  if h : i ≤ n then
    Matrix.det (Matrix.of fun (j l : Fin i) => inner ℝ (b (Fin.castLE h j)) (b (Fin.castLE h l)))
  else 0

/-- `D = ∏_{i=1}^{n−1} d_i` of (1.23). -/
def potD {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) : ℝ :=
  ∏ i ∈ Finset.Ioo 0 n, gram b i

/-- `m(L) = min{|x|² : x ∈ L, x ≠ 0}` of (1.23), written as an infimum. -/
def minSqNorm {n : ℕ} (L : Submodule ℤ (LLLFactor.RedBasis.Vec n)) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ L, x ≠ 0 ∧ r = ‖x‖ ^ 2}

end
end LLLFactor.Reduction
