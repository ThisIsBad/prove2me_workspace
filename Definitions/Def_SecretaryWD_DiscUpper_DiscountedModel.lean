import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace SecretaryWD.DiscUpper

/-- The offline optimum on arrival order `π`: `OPT(π) = max_t d(t) · v(π(t))`. -/
noncomputable def optValue {n : ℕ} (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ⨆ t : Fin n, d t * v (π t)

/-- `E_π[OPT]`, the expected offline optimum over the uniform arrival order. -/
noncomputable def expectedOpt {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  uniformAvg fun π => optValue d v π

/-- The maximum discount `d_max = max_t d(t)`. -/
noncomputable def dmax {n : ℕ} (d : Fin n → ℝ) : ℝ := ⨆ t : Fin n, d t

/-- The maximum value `v_max = max_e v(e)`. -/
noncomputable def vmax {n : ℕ} (v : Fin n → ℝ) : ℝ := ⨆ e : Fin n, v e

/-- `t` is *the* optimal time on order `π`: it attains `max_s d(s) v(π(s))`, and it is the
smallest time that does. -/
def IsOptTime {n : ℕ} (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n) : Prop :=
  (∀ s : Fin n, d s * v (π s) ≤ d t * v (π t)) ∧
    ∀ s : Fin n, s < t → d s * v (π s) < d t * v (π t)

/-- The `c`-th discount class `P_c = {i : d(i) ∈ (2^{-c} d_max, 2^{-(c-1)} d_max]}`, written
as `d_max / 2^c < d(i) ≤ 2 d_max / 2^c`. -/
noncomputable def discountClass {n : ℕ} (d : Fin n → ℝ) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => dmax d / 2 ^ c < d i ∧ d i ≤ 2 * dmax d / 2 ^ c

open Classical in
/-- `OPT_c`: the part of `E_π[OPT]` earned at times of class `c`,
`OPT_c = E_π[ ∑_{i ∈ P_c} 1{i is the optimal time} · d(i) v(π(i)) ]`. -/
noncomputable def optClass {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) : ℝ :=
  uniformAvg fun π =>
    ∑ t ∈ discountClass d c, if IsOptTime d v π t then d t * v (π t) else 0

end SecretaryWD.DiscUpper
