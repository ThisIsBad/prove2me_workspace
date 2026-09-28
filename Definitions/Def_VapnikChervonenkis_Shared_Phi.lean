import Mathlib

namespace VapnikChervonenkis.Shared

/-- The function `Φ(n, r)` of Vapnik and Chervonenkis (1971), p. 266, defined by the
recurrence relation (1):
`Φ(n, r) = Φ(n, r - 1) + Φ(n - 1, r - 1)`, `Φ(0, r) = 1`, `Φ(n, 0) = 1`.
(The paper introduces `Φ(n, r)` as the maximal number of regions into which `r` hyperplanes cut
`n`-dimensional space, but every later use, e.g. Lemma 1, takes it "defined by the recurrence
relation (1)"; that recurrence is the definition here.) -/
def Phi : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, r + 1 => Phi (n + 1) r + Phi n r

end VapnikChervonenkis.Shared
