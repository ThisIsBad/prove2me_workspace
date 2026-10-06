import Mathlib

namespace NonuniformCompetitive.Snoopy

/-- The constant `e_p = (1 + 1/p)^p` of Karlin–Manasse–McGeoch–Owicki (Algorithmica 11 (1994),
§3.2, p. 551), for a block-transfer cost `p`. In the snoopy-caching model `p` is a positive
integer (a block of `p − 1` variables costs `p` bus cycles to transfer); every statement of this
mission that uses `ep p` assumes `1 ≤ p`. (At `p = 0` Lean's `1 / 0 = 0` gives `ep 0 = 1`; that
value is never used.) -/
noncomputable def ep (p : ℕ) : ℝ := (1 + 1 / (p : ℝ)) ^ p

end NonuniformCompetitive.Snoopy
