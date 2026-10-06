import Mathlib

namespace SecretaryWD.DiscLower

open Finset

/-- The horizon `n = L^{4c}` with `L = c` (§4.1.1, p. 6). -/
def horizon (c : ℕ) : ℕ := c ^ (4 * c)

/-- The block ends `n_t = L^{2t}` (§4.1.1, p. 6), `L = c`; `n_{2c} = n`. -/
def blockEnd (c t : ℕ) : ℕ := c ^ (2 * t)

/-- The large value `K = n²` (§4.1.1, p. 6: "say n²"). -/
def bigK (c : ℕ) : ℕ := horizon c ^ 2

/-- The discount class of the 0-based time index `j` (paper time `j + 1`): `1` if
`j + 1 ≤ n_1`, and `t` if `n_{t−1} < j + 1 ≤ n_t` (`2 ≤ t ≤ 2c`). Computed as one plus the
number of `s ∈ {1, …, 2c}` with `n_s < j + 1`. -/
def discountClass (c j : ℕ) : ℕ :=
  1 + ((Icc 1 (2 * c)).filter (fun s => c ^ (2 * s) < j + 1)).card

/-- The step discount function of §4.1.1 (p. 6): `d(j) = L^{−1}` for `1 ≤ j ≤ n_1` and
`d(j) = L^{−t}` for `n_{t−1} < j ≤ n_t`, here on 0-based indices. -/
noncomputable def discount (c : ℕ) : Fin (horizon c) → ℝ :=
  fun j => ((c : ℝ) ^ discountClass c j.val)⁻¹

/-- The value level of the 0-based element `e` in instance `I_t`: the largest `s ≤ t` with
`e < n / n_s` (equivalently `e · n_s < n`), or `0` if there is none (`e ≥ n / n_1`). -/
def valueLevel (c t e : ℕ) : ℕ :=
  ((Icc 1 t).filter (fun s => e * c ^ (2 * s) < horizon c)).card

/-- The instance `I_t` of §4.1.1 (p. 6), `1 ≤ t ≤ 2c`: element `e` has value `K^s` where
`s = valueLevel c t e`, and value `0` if that level is `0`. Thus `I_t` has `n / n_t` elements of
value `K^t`, `n / n_s − n / n_{s+1}` of value `K^s` for `1 ≤ s < t`, and the rest are `0`;
`I_{t+1}` arises from `I_t` by raising `n / n_{t+1}` of its `K^t`'s to `K^{t+1}`. -/
noncomputable def hardInstance (c t : ℕ) : Fin (horizon c) → ℝ :=
  fun e => if valueLevel c t e.val = 0 then 0 else (bigK c : ℝ) ^ valueLevel c t e.val

end SecretaryWD.DiscLower
