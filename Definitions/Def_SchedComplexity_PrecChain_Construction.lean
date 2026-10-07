import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model

namespace SchedComplexity.PrecChain

/-- The number of added jobs in the proof of Theorem 1(l) (p. 9): `n'' = (n' − 1) y'`. The
paper chooses `0 ≤ y' ≤ n' p_*`, so `n' = 0` forces `y' = 0` and the truncated subtraction of
`ℕ` never matters. -/
def nNew (n' y' : ℕ) : ℕ := (n' - 1) * y'

/-- The threshold `y = n y' + ½ n'' (n'' + 1)` of the proof of Theorem 1(l) (p. 9), with
`n = n' + n''`, computed in `ℚ` exactly as printed. -/
def chainThresholdQ (n' y' : ℕ) : ℚ :=
  ((n' + nNew n' y' : ℕ) : ℚ) * y' + (1 / 2 : ℚ) * (nNew n' y' : ℚ) * ((nNew n' y' : ℚ) + 1)

/-- The same threshold as a natural number: `n'' (n'' + 1)` is even, so the division by `2` is
exact and `(chainThreshold n' y' : ℚ) = chainThresholdQ n' y'`. -/
def chainThreshold (n' y' : ℕ) : ℕ :=
  (n' + nNew n' y') * y' + nNew n' y' * (nNew n' y' + 1) / 2

/-- The instance of `P` built from an instance `I` of `P'` and a threshold `y'` in the proof of
Theorem 1(l) (p. 9): keep the `n'` jobs of `I`, the `m` machines, the processing times and the
precedence constraints of `I`, and add `n'' = (n' − 1) y'` jobs `J_{n'+k}` (`k = 1, …, n''`)
with `p_{n'+k,1} = 1` and `J_j < J_{n'+k}` for `j = 1, …, n' + k − 1`. With 0-based indices the
added jobs are `n', …, n' + n'' − 1`; a job `k ≥ n'` has processing time `1` and is preceded by
exactly the jobs `j < k`. No job is required to precede a job of `I` except as in `I`. -/
def chainExtend (I : Instance) (y' : ℕ) : Instance where
  n := I.n + nNew I.n y'
  m := I.m
  p := fun j => if h : (j : ℕ) < I.n then I.p ⟨j, h⟩ else 1
  prec := fun j k =>
    if hk : (k : ℕ) < I.n then
      (if hj : (j : ℕ) < I.n then I.prec ⟨j, hj⟩ ⟨k, hk⟩ else false)
    else decide ((j : ℕ) < k)

end SchedComplexity.PrecChain
