import Mathlib

namespace VeinottWagnerSS.Bounds

open scoped ENNReal

/-- The `(s, S)` ordering rule of Veinott & Wagner (1965), p. 529: with `s ≤ S`, if the stock on
hand plus on order `X` has fallen below `s` (`X < s`), order up to `S`; otherwise order nothing.
`sSRule s S X` is the resulting level `Y` after ordering. -/
def sSRule (s S X : ℤ) : ℤ := if X < s then S else X

/-- A (general, history-dependent) ordering policy for the periodic-review model (p. 527).
`Y t x h` is the level `Y_{t+1}` of stock on hand plus on order after ordering in period `t + 1`
(periods are numbered `1, 2, ⋯` in the paper and `0, 1, ⋯` here), as a function of the initial
level `X₁ = x` and the demands `h = (ξ₁, ⋯, ξ_t)` of the first `t` periods. Since every earlier
`X` and `Y` is determined by `x` and these demands, this is exactly the paper's "any integer
valued function of the information accumulated up to the beginning of period t"; it cannot see
the demand of the current or of any later period. -/
abbrev Policy : Type := (t : ℕ) → ℤ → (Fin t → ℕ) → ℤ

/-- The level `X_{t+1}` of stock on hand plus on order before ordering in period `t + 1`, when
policy `Y` is used from `X₁ = x` and the first `t` demands are `h = (ξ₁, ⋯, ξ_t)`:
`X₁ = x` and `X_{t+1} = Y_t − ξ_t` (p. 527, full backlogging, so levels may be negative). -/
def state (Y : Policy) (x : ℤ) : (t : ℕ) → (Fin t → ℕ) → ℤ
  | 0, _ => x
  | t + 1, h => Y t x (Fin.init h) - (h (Fin.last t) : ℤ)

/-- A policy is admissible if orders are non-negative, `Y_t ≥ X_t`, in every period and along
every demand history (p. 527). -/
def Admissible (Y : Policy) : Prop :=
  ∀ (t : ℕ) (x : ℤ) (h : Fin t → ℕ), state Y x t h ≤ Y t x h

/-- The probability `∏_{i} φ(ξ_i)` of the demand history `h = (ξ₁, ⋯, ξ_t)` when the demands are
i.i.d. with distribution `φ` (p. 526). -/
noncomputable def weight (φ : PMF ℕ) {t : ℕ} (h : Fin t → ℕ) : ℝ≥0∞ :=
  ∏ i, φ (h i)

/-- The probability `E δ(Y_{t+1} − X_{t+1})` that an order is placed in period `t + 1`
(`δ(0) = 0`, `δ(z) = 1` for `z > 0`, p. 527). -/
noncomputable def orderProb (φ : PMF ℕ) (Y : Policy) (x : ℤ) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : Fin t → ℕ, weight φ h * (if state Y x t h < Y t x h then 1 else 0)

/-- The expectation `E G_α(Y_{t+1})` in the extended reals: the expectation of the positive part
minus that of the negative part, each computed in `[0, ∞]`. It is `+∞` when the positive part has
infinite expectation and the negative part does not. -/
noncomputable def expectedG (φ : PMF ℕ) (G : ℤ → ℝ) (Y : Policy) (x : ℤ) (t : ℕ) : EReal :=
  ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h)) : ℝ≥0∞) : EReal) -
    ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h)) : ℝ≥0∞) : EReal)

/-- The expected cost `K E δ(Y_{t+1} − X_{t+1}) + E G_α(Y_{t+1})` of period `t + 1`. -/
noncomputable def periodCost (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Y : Policy) (x : ℤ) (t : ℕ) :
    EReal :=
  (K : EReal) * (orderProb φ Y x t : EReal) + expectedG φ G Y x t

/-- The `n`-period cost of Eq. (2), p. 529:
`f_n(x | Y) = ∑_{t=1}^{n} α^{t−1} [K E δ(Y_t − X_t) + E G_α(Y_t)]` with `X₁ = x`,
valued in the extended reals (it is `+∞` for policies of infinite expected cost). -/
noncomputable def cost (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (x : ℤ) (Y : Policy) : EReal :=
  ∑ t ∈ Finset.range n, ((α ^ t : ℝ) : EReal) * periodCost φ G K Y x t

/-- `Y` is an optimal policy for the `n`-period model (p. 529): it is admissible and
`f_n(x | Y) ≤ f_n(x | Y')` for every admissible policy `Y'` and every initial level `x`. -/
def IsOptimal (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (Y : Policy) : Prop :=
  Admissible Y ∧ ∀ Y' : Policy, Admissible Y' → ∀ x : ℤ, cost φ G K α n x Y ≤ cost φ G K α n x Y'

/-- Policy `Y` uses the `(s, S)` rule in period `t + 1`:
`Y_{t+1} = S` if `X_{t+1} < s` and `Y_{t+1} = X_{t+1}` if `X_{t+1} ≥ s`, along every history. -/
def UsesRule (Y : Policy) (t : ℕ) (s S : ℤ) : Prop :=
  ∀ (x : ℤ) (h : Fin t → ℕ), Y t x h = sSRule s S (state Y x t h)

/-- `Y` is an `(s, S)` policy for the `n`-period model (p. 529): for each period `t + 1 ≤ n` there
are integers `s t ≤ S t` such that `Y` uses the `(s t, S t)` rule in period `t + 1`. -/
def IsSSPolicy (n : ℕ) (Y : Policy) : Prop :=
  ∃ s S : ℕ → ℤ, ∀ t < n, s t ≤ S t ∧ UsesRule Y t (s t) (S t)

end VeinottWagnerSS.Bounds
