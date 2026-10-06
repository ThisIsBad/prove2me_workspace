import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model

namespace AlgMechDesign.Randomized

open Finset

/-- The other agent of a two-agent instance: the paper's `i' = 3 − i` on agents `{1, 2}`, which on
`Fin 2 = {0, 1}` is `1 - i` (so `other 0 = 1`, `other 1 = 0`). -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- The allocation of the biased min work mechanism (Fig. 1, p. 182) with parameters `β` and
`s ∈ {1, 2}ᵏ` on declarations `t`: task `j` goes to the favoured agent `i = s j` if
`tⁱ_j ≤ β · t^{i'}_j`, and to the other agent `i'` otherwise. -/
noncomputable def bmwAlloc {k : ℕ} (β : ℝ) (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) :
    Fin k → Fin 2 :=
  fun j => if t (s j) j ≤ β * t (other (s j)) j then s j else other (s j)

/-- The payments of the biased min work mechanism (Fig. 1): for each task `j` with favoured agent
`i = s j`, if `i` gets `j` it is paid `β · t^{i'}_j`; otherwise the other agent `i'` gets `j` and
is paid `β⁻¹ · tⁱ_j`. The payment to an agent is the sum over the tasks it receives. -/
noncomputable def bmwPay {k : ℕ} (β : ℝ) (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ)
    (i : Fin 2) : ℝ :=
  ∑ j, if bmwAlloc β s t j = i then
      (if i = s j then β * t (other (s j)) j else β⁻¹ * t (s j) j)
    else 0

/-- The biased min work allocations with `β = 4/3` (Def. 17), indexed by `s ∈ {1, 2}ᵏ`. -/
noncomputable def rbmwAlloc {k : ℕ} (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) :
    Fin k → Fin 2 :=
  bmwAlloc (4 / 3) s t

/-- The biased min work payments with `β = 4/3` (Def. 17), indexed by `s ∈ {1, 2}ᵏ`. -/
noncomputable def rbmwPay {k : ℕ} (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) (i : Fin 2) : ℝ :=
  bmwPay (4 / 3) s t i

/-- The objective of the randomly biased min work mechanism (Defs. 15, 17): the expected make-span
when `s` is uniform on `{1, 2}ᵏ`, i.e. the average of the make-spans over all `2ᵏ` vectors `s`. -/
noncomputable def expMakespan {k : ℕ} (t : Fin 2 → Fin k → ℝ) : ℝ :=
  (1 / 2 ^ k) * ∑ s : Fin k → Fin 2, makespan t (rbmwAlloc s t)

end AlgMechDesign.Randomized
