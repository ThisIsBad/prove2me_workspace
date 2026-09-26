import Mathlib

namespace RevenueManagement

/-! ### Overbooking, Chapter 4 of Talluri and van Ryzin -/

/-! #### The dynamic overbooking model, Sect. 4.3.1 -/

/-- The binomial pmf `P(Bin(x, q) = k)`. -/
noncomputable def binomPmf (q : ℝ) (x k : ℕ) : ℝ := (x.choose k : ℝ) * q ^ k * (1 - q) ^ (x - k)

/-- The data of the dynamic overbooking model: horizon `T`, capacity `C`, denied-service cost
`c`, revenue `p t` per reservation accepted in period `t`, refund `r t` per cancellation in period
`t`, survival probability `q t` of a reservation over period `t`, and the pmf `f t` of the demand
`D_t` for new reservations in period `t`. -/
structure DynOverbooking where
  T : ℕ
  C : ℕ
  c : ℕ → ℝ
  p : ℕ → ℝ
  r : ℕ → ℝ
  q : ℕ → ℝ
  f : ℕ → ℕ → ℝ

/-- The model's assumptions: each `f t` is a pmf on `ℕ`, `0 ≤ q t ≤ 1`, `p t ≥ 0`, `r t ≥ 0`, and
`c` is a cost penalizing denied service: `c 0 = 0` and `c k ≥ 0`. (4.11) never reads `c 0`, so
without `c 0 = 0` a sequence convex on `ℕ` need not make the terminal value concave. -/
def DynOverbooking.IsModel (M : DynOverbooking) : Prop :=
  (∀ t, (∀ d, 0 ≤ M.f t d) ∧ HasSum (M.f t) 1) ∧ (∀ t, 0 ≤ M.q t ∧ M.q t ≤ 1) ∧
    (∀ t, 0 ≤ M.p t) ∧ (∀ t, 0 ≤ M.r t) ∧ M.c 0 = 0 ∧ (∀ k, 0 ≤ M.c k)

/-- `c` is convex on `ℕ`: nondecreasing differences. -/
def IsConvexSeq (c : ℕ → ℝ) : Prop := ∀ k, c (k + 1) - c k ≤ c (k + 2) - c (k + 1)

/-- The value function with `k` periods to go (period `t = T + 1 − k`) and `y` reservations on
hand: the terminal value (4.11) with no period to go, and otherwise the recursion of Sect. 4.3.1,
`V_t(y) = E[max_{y ≤ x ≤ y + D_t} {v_{t+1}(x) + (x − y) p(t)}]` with
`v_{t+1}(x) = E[V_{t+1}(Z_t(x)) − (x − Z_t(x)) r(t)]`, `Z_t(x) ~ Bin(x, q_t)`. -/
noncomputable def DynOverbooking.valueGo (M : DynOverbooking) : ℕ → ℕ → ℝ
  | 0, y => if y ≤ M.C then 0 else -(M.c (y - M.C))
  | k + 1, y => ∑' d, M.f (M.T - k) d *
      (Finset.Icc y (y + d)).sup' ⟨y, Finset.mem_Icc.2 ⟨le_rfl, Nat.le_add_right _ _⟩⟩ (fun x =>
        (∑ z ∈ Finset.range (x + 1), binomPmf (M.q (M.T - k)) x z *
          (M.valueGo k z - ((x : ℝ) - z) * M.r (M.T - k))) + ((x : ℝ) - y) * M.p (M.T - k))

/-- `V_t(y)` for `t = 1, …, T + 1`. -/
noncomputable def DynOverbooking.value (M : DynOverbooking) (t y : ℕ) : ℝ :=
  M.valueGo (M.T + 1 - t) y

/-- `v_{t+1}(x) = E[V_{t+1}(Z_t(x)) − (x − Z_t(x)) r(t)]`, the value of ending period `t` with `x`
reservations before cancellations. -/
noncomputable def DynOverbooking.postValue (M : DynOverbooking) (t x : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (x + 1), binomPmf (M.q t) x z * (M.value (t + 1) z - ((x : ℝ) - z) * M.r t)

/-- `v_{t+1}(x) + x p(t)`, the objective whose maximizer is the overbooking limit of period `t`. -/
noncomputable def DynOverbooking.limitObjective (M : DynOverbooking) (t x : ℕ) : ℝ :=
  M.postValue t x + x * M.p t

/-- `x` is an optimal booking level in period `t` with `y` reservations on hand and `d` new
requests: `y ≤ x ≤ y + d` and it maximizes `v_{t+1}(x) + (x − y) p(t)` over that range. -/
def DynOverbooking.IsOptimalLevel (M : DynOverbooking) (t y d x : ℕ) : Prop :=
  y ≤ x ∧ x ≤ y + d ∧ ∀ x', y ≤ x' → x' ≤ y + d →
    M.postValue t x' + ((x' : ℝ) - y) * M.p t ≤ M.postValue t x + ((x : ℝ) - y) * M.p t

/-- The greatest optimal overbooking limit `x*(t)`: the largest `x` at which
`v_{t+1}(x) + x p(t)` is at least its value at every smaller level, as an element of `ℕ∞`, `⊤`
when accepting is always better. -/
noncomputable def DynOverbooking.overbookingLimit (M : DynOverbooking) (t : ℕ) : ℕ∞ :=
  sSup ((fun x : ℕ => (x : ℕ∞)) ''
    {x | ∀ x' ≤ x, M.limitObjective t x' ≤ M.limitObjective t x})

/-- The overbooking-limit policy with limit `L`: with `y` on hand and `d` requests, accept new
reservations until the total reaches `L`, i.e. book `min {y + d, max {y, L}}`. -/
noncomputable def limitPolicy (L : ℕ∞) (y d : ℕ) : ℕ :=
  (min ((y + d : ℕ) : ℕ∞) (max (y : ℕ∞) L)).toNat

/-! #### Substitutable capacity, Sect. 4.5 -/

/-- The Poisson pmf `P(Poisson(μ) = k)`. -/
noncomputable def poissonPmf (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ) * μ ^ k / k.factorial

/-- The service-period transportation problem (TP): the maximum net benefit `V(z, C)` of assigning
`z_j` surviving customers of each class `j : Fin n` to the resources `i : Fin (m+1)`, where
resource `0` is the virtual denied-service resource (uncapacitated) and resource `i ≠ 0` has
capacity `Cap i`; `h j i` is the net benefit of assigning a class-`j` customer to resource `i`. -/
noncomputable def serviceValue {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (z : Fin n → ℕ) : ℝ :=
  sSup {w | ∃ a : Fin n → Fin (m + 1) → ℝ, (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = z j) ∧
    (∀ i, i ≠ 0 → ∑ j, a j i ≤ Cap i) ∧ w = ∑ j, ∑ i, h j i * a j i}

/-- The expected net revenue `G(x)` of Eq. (4.21) for final overbooking levels `x` given `y`
reservations on hand, with show demands `Z_j ~ Poisson(q_j x_j)` independent across classes:
`pᵀ(x − y) − E[sᵀ(x − Z(x))] + E[V(Z(x), C)]`. -/
noncomputable def expNetRevenue {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (p s q : Fin n → ℝ) (y x : Fin n → ℕ) : ℝ :=
  ∑ j, p j * ((x j : ℝ) - y j) +
    ∑' z : Fin n → ℕ, (∏ j, poissonPmf (q j * x j) (z j)) *
      (serviceValue h Cap z - ∑ j, s j * ((x j : ℝ) - z j))

/-- The greatest optimal booking limit of class `i` when the other classes are held at the levels
of `x`: the largest `k` at which `G(x with x_i := k)` is at least its value at every smaller `k`,
as an element of `ℕ∞`. -/
noncomputable def jointLimit {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (p s q : Fin n → ℝ) (y x : Fin n → ℕ) (i : Fin n) : ℕ∞ :=
  sSup ((fun k : ℕ => (k : ℕ∞)) '' {k | ∀ k' ≤ k,
    expNetRevenue h Cap p s q y (Function.update x i k') ≤
      expNetRevenue h Cap p s q y (Function.update x i k)})

end RevenueManagement
