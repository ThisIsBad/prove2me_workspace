import Mathlib

namespace VapnikChervonenkis.Shared

open MeasureTheory

open Classical in
/-- The relative frequency `ν_A^(l)(x_1, …, x_l) = n_A / l` of the event `A` in the sample
`x : Fin l → X` (Introduction, p. 264): the number of sample terms lying in `A`, divided by
the sample size. -/
noncomputable def relFreq {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) : ℝ :=
  ((Finset.univ.filter (fun i => x i ∈ A)).card : ℝ) / l

/-- The maximal deviation `π^(l) = sup_{A ∈ S} |ν_A^(l) − P_A|` between relative frequency and
probability over the class `S` (p. 265), as a function of the sample `x : Fin l → X`. The
supremum runs over the events of `S`; for `S = ∅` it is `0`. -/
noncomputable def maxDeviation {X : Type*} [MeasurableSpace X] (S : Set (Set X))
    (P : Measure X) (l : ℕ) (x : Fin l → X) : ℝ :=
  ⨆ A : S, |relFreq (A : Set X) x - P.real (A : Set X)|

/-- The maximal difference of relative frequencies between the two semi-samples,
`ρ^(l) = sup_{A ∈ S} |ν′_A − ν″_A|` (§1.3, p. 268), as a function of the double sample
`x : Fin (l + l) → X`: the first semi-sample is `x_1, …, x_l` (indices `Fin.castAdd`), the
second `x_{l+1}, …, x_{2l}` (indices `Fin.natAdd`). For `S = ∅` it is `0`. -/
noncomputable def semiSampleDeviation {X : Type*} (S : Set (Set X)) (l : ℕ)
    (x : Fin (l + l) → X) : ℝ :=
  ⨆ A : S, |relFreq (A : Set X) (fun i : Fin l => x (Fin.castAdd l i))
    - relFreq (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))|

end VapnikChervonenkis.Shared
