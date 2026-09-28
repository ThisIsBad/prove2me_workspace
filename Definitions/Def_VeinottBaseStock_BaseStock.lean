import Mathlib
import Definitions.Def_VeinottBaseStock_Model

open MeasureTheory

namespace VeinottBaseStock

variable {n m : ℕ}

/-- Hypothesis (3a) (p. 210): for each period, `ȳ_i` minimizes `G_i(y)` over the set `Y_i`. -/
def Model.H3a (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, ybar k ∈ M.Y k ∧ ∀ y ∈ M.Y k, M.G k (ybar k) ≤ M.G k y

/-- Hypothesis (3b) (p. 210): `q_{i+1}(s_i(ȳ_i, t)) ≤ ȳ_{i+1}` for all `t ∈ 𝔇_i`. -/
def Model.H3b (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, ∀ t ∈ M.Dset k, M.q (k + 1) (M.s k (ybar k) t) ≤ coeVec (ybar (k + 1))

/-- Hypothesis (3c) (p. 212): each `Y_i` is closed and linearly ordered by `≤`. -/
def Model.H3c (M : Model n m) : Prop :=
  ∀ k, IsClosed (M.Y k) ∧ IsChain (· ≤ ·) (M.Y k)

/-- Hypothesis (3d) (p. 212), with its `q`-clause in the one-sided form used by the proof of
Theorem 3.2: `G_i` and `s_i(·, t)` (`t ∈ 𝔇_i`) are nondecreasing on `{y ∈ Y_i | y ≥ ȳ_i}`, and
for `x ≤ x'` in `X_i` with `q_i(x) ≰ ȳ_i` one has `q_i(x) ≤ q_i(x')`. -/
def Model.H3d (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  (∀ k, MonotoneOn (M.G k) {y | y ∈ M.Y k ∧ ybar k ≤ y}) ∧
  (∀ k, ∀ t ∈ M.Dset k, MonotoneOn (fun y => M.s k y t) {y | y ∈ M.Y k ∧ ybar k ≤ y}) ∧
  (∀ k, ∀ x ∈ M.X k, ∀ x' ∈ M.X k, x ≤ x' → ¬ M.q k x ≤ coeVec (ybar k) → M.q k x ≤ M.q k x')

/-- Every admissible initial inventory vector admits an admissible order:
for `x ∈ X_i` there is `y ∈ Y_i` with `y ≥ q_i(x)`. The paper uses this without stating it (p. 212,
nonemptiness of the set whose minimal element is `w_i(x)`). -/
def Model.OrderFeasible (M : Model n m) : Prop :=
  ∀ k, ∀ x ∈ M.X k, ∃ y ∈ M.Y k, M.q k x ≤ coeVec y

/-- The set `Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` (p. 212). -/
def Model.orderSet (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  M.Y k ∩ {y | M.q k x ≤ coeVec y ∧ ybar k ≤ y}

open Classical in
/-- `w_i(x)`: the minimal (least) element of `Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` (p. 212); when that
set has no least element the value is `ȳ_i` (a convention; it keeps `w_i` inside `Y_i` under (3a)). -/
noncomputable def Model.w (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  if h : ∃ a, IsLeast (M.orderSet ybar k x) a then h.choose else ybar k

open Classical in
/-- The base stock ordering rule of Theorem 3.2 (p. 213): order up to `ȳ_i` if `q_i(x) ≤ ȳ_i`,
otherwise up to `w_i(x)`. -/
noncomputable def Model.baseStockRule (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  if M.q k x ≤ coeVec (ybar k) then ybar k else M.w ybar k x

/-- The initial inventory vector `x*_{k+1}` when the base stock rule is followed from `x₁` along the
demand path `d`. -/
noncomputable def Model.baseStockState (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₁
  | k + 1 => M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k)

/-- Extends a finite demand history `(d_1, …, d_k)` to a demand path (by `0` afterwards; the
base stock state in period `k` only reads the first `k` demands). -/
def extendHist {k : ℕ} (z : Fin k → Fin m → ℝ) : ℕ → Fin m → ℝ :=
  fun j => if h : j < k then z ⟨j, h⟩ else 0

/-- The base stock ordering policy `Ȳ*` of Theorem 3.2 (p. 213), as a policy on demand
histories: in period `k` it applies the base stock rule to the current inventory vector `x*_{k+1}`
obtained by following the rule from `x₁`. -/
noncomputable def Model.baseStock (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ) :
    Pol n m :=
  fun k z => M.baseStockRule ybar k (M.baseStockState ybar x₁ (extendHist z) k)

end VeinottBaseStock
