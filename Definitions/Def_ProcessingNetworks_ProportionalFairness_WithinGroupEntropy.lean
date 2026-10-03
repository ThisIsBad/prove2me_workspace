import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore

namespace ProcessingNetworks.ProportionalFairness

/-- The upper-right Dini derivative `D⁺f(t)`, Appendix A.4, Eq. (A.9), restated identically from
mission IX (which itself restates mission V's `LyapunovCriteria.diniUpperRight`); `EReal`-valued,
so that `±∞` values are represented as such rather than by a junk real. -/
noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The upper-left Dini derivative `D⁻f(t)`, Appendix A.4, Eq. (A.10) — new to this chunk (mission
IX only needed `D⁺`): `D⁻f(t) := limsup_{h ↓ 0} (f(t) - f(t-h))/h`. -/
noncomputable def diniUpperLeft (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f t - f (t - h)) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The entropy Lyapunov function `φ` (Eqs. 10.38-10.39), restated identically from mission IX
(`Ḋᵢ(t)` the right derivative, which for a PF fluid model solution exists and is positive
whenever `Zᵢ(t) > 0`). -/
noncomputable def phi {I : ℕ} (Dh Zh : ℝ → Fin I → ℝ) (alpha : Fin I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if Zh t i = 0 then 0 else
    Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i)

/-- The within-group entropy term `f` (Eq. 10.50, renamed `withinGroupEntropy` to avoid colliding
with the PF objective `f` of Eq. 10.2 — the book itself reuses the letter `f` for two different
quantities within this chapter): `f(t) := ∑_ℓ ∑_{i∈I(ℓ)} Z_i(t) log(Z_i(t)/Y_ℓ(t))`, with the term
for class `i` defined to be `0` when `Z_i(t) = 0` (conventions 10.46: `0/0=0`, `0log(0)=0`). Since
`Z_i(t) ≤ Y_{grp i}(t)` always, the ratio is a genuine real number in `[0,1]` whenever `Z_i(t) >
0`, so `Real.log` (not an extended log) suffices here — unlike the PF objective `f`, this term
never needs `-∞`. -/
noncomputable def withinGroupEntropy {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (t : ℝ) : ℝ :=
  ∑ i, if Zh t i = 0 then 0 else Zh t i * Real.log (Zh t i / groupAggregate grp (Zh t) (grp i))

end ProcessingNetworks.ProportionalFairness
