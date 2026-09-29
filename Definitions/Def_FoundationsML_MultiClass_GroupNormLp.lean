import Mathlib

namespace FoundationsML.MultiClass

/-- The `L_{H,p}` group norm of a tuple of Hilbert-space weight vectors
`W = (w_1,…,w_k)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 219, PDF p. 236): `‖W‖_{H,p} = (∑_{l=1}^k ‖w_l‖_H^p)^{1/p}`. -/
noncomputable def GroupNormLp {Hb : Type*} [NormedAddCommGroup Hb] {k : ℕ}
    (p : ℝ) (W : Fin k → Hb) : ℝ :=
  (∑ l, ‖W l‖ ^ p) ^ (1 / p)

end FoundationsML.MultiClass
