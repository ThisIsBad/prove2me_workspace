import Mathlib

namespace LewisTorczon.BoundPS

/-- The feasible region `Ω = { x ∈ ℝⁿ | ℓ ≤ x ≤ u }` of problem (1)
(Lewis–Torczon, ICASE 96-20, p. 1). The bounds are extended reals, so `ℓ_j = -∞` and
`u_j = +∞` are allowed, as on p. 1 ("by permitting `ℓ_j, u_j = ±∞`"). Points of `ℝⁿ` carry the
Euclidean norm. The paper's coordinate `j = 1, …, n` is Lean's `j : Fin n` (0-based). -/
def box {n : ℕ} (lo hi : Fin n → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, lo j ≤ ((x j : ℝ) : EReal) ∧ ((x j : ℝ) : EReal) ≤ hi j}

/-- The scalar projection `p_j(t)` of p. 2: `ℓ_j` if `t < ℓ_j`, `t` if `ℓ_j ≤ t ≤ u_j`,
`u_j` if `t > u_j`, computed as `max ℓ_j (min u_j t)` in `EReal`. When `a < b` the value is
finite (e.g. `a = -∞`, `t < b` gives `t`; `a = -∞`, `b = +∞` gives `t`), so `toReal` loses
nothing. -/
noncomputable def clampCoord (a b : EReal) (t : ℝ) : ℝ :=
  (max a (min b (t : EReal))).toReal

/-- The projection onto `Ω`, `P(x) = Σ_j p_j(x_j) e_j` (p. 2). -/
noncomputable def boxProj {n : ℕ} (lo hi : Fin n → EReal) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => clampCoord (lo j) (hi j) (x j))

/-- The feasible level set `L_Ω(y) = { x ∈ Ω | f(x) ≤ f(y) }` (p. 2). -/
def levelSet {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ box lo hi ∧ f x ≤ f y}

end LewisTorczon.BoundPS
