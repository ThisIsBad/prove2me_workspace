import Mathlib

namespace NonmonotoneSubmod.QueryLB

/-- The two-regime function `f(k, ℓ)` of the proof of Theorem 4.5
(Feige–Mirrokni–Vondrák 2011, pp. 1149–1150), with `ϵn = m`:
* if `|k − ℓ| ≤ m`: `f(k, ℓ) = (k + ℓ)(n − k − ℓ)`;
* otherwise: `f(k, ℓ) = k(n − 2ℓ) + (n − 2k)ℓ + m² − 2m|k − ℓ|`.
The two expressions agree on `|k − ℓ| = m`; the first is used there. -/
noncomputable def fkl (n m k l : ℕ) : ℝ :=
  if |(k : ℝ) - l| ≤ m then ((k : ℝ) + l) * ((n : ℝ) - k - l)
  else (k : ℝ) * ((n : ℝ) - 2 * l) + ((n : ℝ) - 2 * k) * l + (m : ℝ) ^ 2
    - 2 * (m : ℝ) * |(k : ℝ) - l|

/-- The hard instance `f_C` on `[n]` for the partition `(C, D)`, `D = Cᶜ`:
`f_C(S) = f(|S ∩ C|, |S ∩ D|)` (p. 1149). -/
noncomputable def fC (n m : ℕ) (C : Finset (Fin n)) (S : Finset (Fin n)) : ℝ :=
  fkl n m (S ∩ C).card (S ∩ Cᶜ).card

/-- The cut function of the complete graph on `[n]`, `g(S) = |S|(n − |S|)` (p. 1150). -/
def gCut (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (S.card : ℝ) * ((n : ℝ) - S.card)

/-- A set `Q` is balanced for the partition `(C, Cᶜ)` when `|Q ∩ C|` and `|Q ∩ Cᶜ|` differ by at
most `m = ϵn`; otherwise it is "unbalanced" (p. 1150). -/
def Balanced (n m : ℕ) (C Q : Finset (Fin n)) : Prop :=
  |((Q ∩ C).card : ℝ) - (Q ∩ Cᶜ).card| ≤ m

noncomputable instance (n m : ℕ) (C Q : Finset (Fin n)) : Decidable (Balanced n m C Q) := by
  unfold Balanced; infer_instance

end NonmonotoneSubmod.QueryLB
