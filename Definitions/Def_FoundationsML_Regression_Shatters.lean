import Mathlib

namespace FoundationsML.Regression

/-- A set of points `{z_1,…,z_m}` is shattered by a family `G` of real-valued functions on `Z`
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Definition 11.4, p. 271, PDF p. 288): there exist threshold witnesses `t_1,…,t_m ∈ ℝ` such
that every sign pattern `b : Fin m → Bool` is realized by some `g ∈ G` via
`b_i ↔ g(z_i) > t_i`.

**Formalization Note.** Following the book's own reformulation (Eq. (11.3), p. 271, PDF p.
288), shattering is stated directly via the thresholded indicator `g(z_i) > t_i` rather than
the sign function `sgn(g(z_i) − t_i)`; the two agree except at the measure-zero boundary
`g(z_i) = t_i` (where `sgn` gives `0`, not a valid Boolean sign, so the book's own definition
implicitly also excludes this case from mattering for the shattering count of `2^m` distinct
patterns). -/
def Shatters {Z : Type*} (G : Set (Z → ℝ)) {m : ℕ} (z : Fin m → Z) : Prop :=
  ∃ t : Fin m → ℝ, ∀ b : Fin m → Bool, ∃ g ∈ G, ∀ i, b i ↔ t i < g (z i)

end FoundationsML.Regression
