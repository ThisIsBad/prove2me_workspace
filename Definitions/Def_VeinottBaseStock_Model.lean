import Mathlib

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- The data of Veinott's multi-product, dynamic, nonstationary inventory model (§2, pp. 207–210).
There are `n` products and `m` demand classes. Periods are indexed from `0`: Lean period `k` is the
paper's period `k + 1`.

* `X k` — admissible initial inventory vectors `x_{k+1}` (a negative coordinate is a backlog);
* `Y k` — admissible inventory vectors after ordering, `y_{k+1}`;
* `Dset k` — the set `𝔇_{k+1}` of values of the demand vector `D_{k+1}`;
* `q k` — the extended-real lower bound on `y` after ordering: `y_{k+1} ≥ q_{k+1}(x_{k+1})`;
* `s k y t` — the end-of-period stock vector `s_{k+1}(y, t) = x_{k+2}`;
* `c k` — the linear ordering cost vector `c_{k+1}`; ordering `y - x` costs `c_{k+1} ⬝ (y - x)`;
* `g k y t` — the holding and shortage cost `g_{k+1}(y, t)`;
* `α k` — the discount factor `α_{k+1}`;
* `Φ k` — the probability law of `D_{k+1}`;
* `γ k` — the constants `γ_{k+1}` of the lower-bound assumption on `G_{k+1}` (p. 210). -/
structure Model (n m : ℕ) where
  X : ℕ → Set (Fin n → ℝ)
  Y : ℕ → Set (Fin n → ℝ)
  Dset : ℕ → Set (Fin m → ℝ)
  q : ℕ → (Fin n → ℝ) → (Fin n → EReal)
  s : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)
  c : ℕ → Fin n → ℝ
  g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ
  α : ℕ → ℝ
  Φ : ℕ → Measure (Fin m → ℝ)
  γ : ℕ → ℝ

/-- A real vector read coordinatewise as an extended-real vector, so that it can be compared with
`q k x`. -/
def coeVec {n : ℕ} (y : Fin n → ℝ) : Fin n → EReal := fun j => ((y j : ℝ) : EReal)

variable {n m : ℕ}

/-- `W_{k+1}(y, t) = c_{k+1} y + g_{k+1}(y, t) - α_{k+1} c_{k+2} s_{k+1}(y, t)` (p. 209). -/
def Model.W (M : Model n m) (k : ℕ) (y : Fin n → ℝ) (t : Fin m → ℝ) : ℝ :=
  M.c k ⬝ᵥ y + M.g k y t - M.α k * (M.c (k + 1) ⬝ᵥ M.s k y t)

/-- `L_{k+1}(y) = ∫_{𝔇_{k+1}} g_{k+1}(y, t) dΦ_{k+1}(t)` (p. 209). -/
noncomputable def Model.L (M : Model n m) (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  ∫ t in M.Dset k, M.g k y t ∂(M.Φ k)

/-- `G_{k+1}(y) = ∫_{𝔇_{k+1}} W_{k+1}(y, t) dΦ_{k+1}(t)` (p. 209). -/
noncomputable def Model.G (M : Model n m) (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  ∫ t in M.Dset k, M.W k y t ∂(M.Φ k)

/-- The discount to period `k + 1`: `β_1 = 1`, `β_{k+1} = α_1 ⋯ α_k` (p. 209). -/
def Model.β (M : Model n m) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, M.α j

/-- The standing assumptions of §2 (pp. 207–210). -/
structure Model.Standing (M : Model n m) : Prop where
  /-- `0 ≤ α_i` (p. 209). -/
  alpha_nonneg : ∀ k, 0 ≤ M.α k
  /-- `𝔇_i` is a Borel set (p. 209). -/
  dset_measurableSet : ∀ k, MeasurableSet (M.Dset k)
  /-- `q_i` is a Borel function (p. 209). -/
  q_measurable : ∀ k, Measurable (M.q k)
  /-- `s_i(·,·)` is a Borel function (p. 209). -/
  s_measurable : ∀ k, Measurable (Function.uncurry (M.s k))
  /-- `g_i(·,·)` is a Borel function (p. 209). -/
  g_measurable : ∀ k, Measurable (Function.uncurry (M.g k))
  /-- The range of `s_i` is `X_{i+1}` (p. 208). -/
  s_mem : ∀ k, ∀ y ∈ M.Y k, ∀ t ∈ M.Dset k, M.s k y t ∈ M.X (k + 1)
  /-- `Φ_i` is a probability distribution (p. 207). -/
  isProbabilityMeasure : ∀ k, IsProbabilityMeasure (M.Φ k)
  /-- `D_i` takes values in `𝔇_i`, so its law is concentrated on `𝔇_i` (p. 207). -/
  Φ_compl_Dset : ∀ k, M.Φ k (M.Dset k)ᶜ = 0
  /-- The integral `L_i(y)` exists and is finite for every `y` (p. 209). -/
  g_integrableOn : ∀ k y, IntegrableOn (M.g k y) (M.Dset k) (M.Φ k)
  /-- The integral `G_i(y)` exists and is finite for every `y` (p. 209). -/
  W_integrableOn : ∀ k y, IntegrableOn (M.W k y) (M.Dset k) (M.Φ k)
  /-- `G_i(y) ≥ γ_i` for all `y` and `i` (p. 210). -/
  G_ge : ∀ k y, M.γ k ≤ M.G k y
  /-- `∑_i |β_i γ_i| < ∞` (p. 210). -/
  summable_β_γ : Summable fun k => |M.β k * M.γ k|

/-- The demand process (p. 207): `D_1, D_2, …` are independent random vectors on a probability
space `(Ω, P)`, `D_i` has law `Φ_i` and takes its values in `𝔇_i`. Lean's `D k` is `D_{k+1}`. -/
structure Model.IsDemandProcess (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) : Prop where
  measurable : ∀ k, Measurable (D k)
  indep : iIndepFun D P
  law : ∀ k, P.map (D k) = M.Φ k
  mem : ∀ k ω, D k ω ∈ M.Dset k

/-- An ordering policy in non-anticipative form: `Ŷ k d̄` is the inventory vector after ordering
in Lean period `k` (paper period `k + 1`) as a function of the demands `d̄ = (D_1, …, D_k)` of the
previous periods (the paper's `Ȳ_{k+1}(D̄_{k+1})`, §5, p. 219). -/
abbrev Pol (n m : ℕ) : Type := (k : ℕ) → (Fin k → Fin m → ℝ) → (Fin n → ℝ)

/-- The inventory vector after ordering in period `k` under the policy `Ŷ` along the demand path
`d`: `y_{k+1} = Ŷ_{k+1}(d_1, …, d_k)`. -/
def Model.orderSeq (_M : Model n m) (Ŷ : Pol n m) (d : ℕ → Fin m → ℝ) (k : ℕ) : Fin n → ℝ :=
  Ŷ k (fun j : Fin k => d j)

/-- The initial inventory vector of period `k` under `Ŷ` along `d`, from the fixed initial vector
`x₁`: `x_1 = x₁`, `x_{k+2} = s_{k+1}(y_{k+1}, d_{k+1})`. -/
def Model.stateSeq (M : Model n m) (Ŷ : Pol n m) (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₁
  | k + 1 => M.s k (M.orderSeq Ŷ d k) (d k)

/-- A feasible ordering policy (pp. 208–209): every decision rule is a Borel function with values
in `Y_i`, and for every possible history (every demand path with `d_i ∈ 𝔇_i`) the order satisfies
`y_i ≥ q_i(x_i)`. -/
structure Model.Feasible (M : Model n m) (x₁ : Fin n → ℝ) (Ŷ : Pol n m) : Prop where
  measurable : ∀ k, Measurable (Ŷ k)
  mem_Y : ∀ k z, Ŷ k z ∈ M.Y k
  q_le : ∀ d : ℕ → Fin m → ℝ, (∀ j, d j ∈ M.Dset j) →
    ∀ k, M.q k (M.stateSeq Ŷ x₁ d k) ≤ coeVec (M.orderSeq Ŷ d k)

/-- The part of the cost (2.4) above the constants `γ_i`:
`∑_k E[β_{k+1} (G_{k+1}(y_{k+1}) - γ_{k+1})] ∈ [0, ∞]`, with the random `y_{k+1}` obtained by
running `Ŷ` along the demand process. -/
noncomputable def Model.excess (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : ENNReal :=
  ∑' k, ∫⁻ ω, ENNReal.ofReal (M.β k * (M.G k (M.orderSeq Ŷ (fun j => D j ω) k) - M.γ k)) ∂P

/-- The expected discounted cost (2.4), `f(x_1 | Ŷ) = ∑_i β_i E G_i(y_i)` with `+∞` allowed:
the extended-real sum of `excess` and the finite real series `∑_i β_i γ_i`. -/
noncomputable def Model.cost (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : EReal :=
  ((M.excess P D Ŷ : ENNReal) : EReal) + ((∑' k, M.β k * M.γ k : ℝ) : EReal)

/-- A policy is optimal (p. 210) if it is feasible and its cost is at most the cost of every
feasible policy. -/
def Model.IsOptimal (M : Model n m) (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : Prop :=
  M.Feasible x₁ Ŷ ∧ ∀ Ŷ' : Pol n m, M.Feasible x₁ Ŷ' → M.cost P D Ŷ ≤ M.cost P D Ŷ'

end VeinottBaseStock
