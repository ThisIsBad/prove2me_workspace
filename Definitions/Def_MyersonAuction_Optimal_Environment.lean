import Mathlib

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

/-- The independent private-value environment of Myerson, §§2–4. -/
structure Environment (ι : Type) [Fintype ι] where
  a : ι → ℝ
  b : ι → ℝ
  a_lt_b : ∀ i, a i < b i
  f : ι → ℝ → ℝ
  f_cont : ∀ i, ContinuousOn (f i) (Set.Icc (a i) (b i))
  f_pos : ∀ i t, t ∈ Set.Icc (a i) (b i) → 0 < f i t
  f_int : ∀ i, ∫ t in a i..b i, f i t = 1
  e : ι → ℝ → ℝ
  e_cont : ∀ i, ContinuousOn (e i) (Set.Icc (a i) (b i))
  t0 : ℝ

def support {ι : Type} [Fintype ι] (E : Environment ι) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (E.a i) (E.b i))

def distribution {ι : Type} [Fintype ι] (E : Environment ι) : Measure (ι → ℝ) :=
  (volume.restrict (support E)).withDensity
    (fun t => ENNReal.ofReal (∏ i, E.f i (t i)))

def F {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (s : ℝ) : ℝ :=
  ∫ u in E.a i..s, E.f i u

def bidderValue {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (i : ι) (t : ι → ℝ) : ℝ :=
  t i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j)

def sellerValue {ι : Type} [Fintype ι] (E : Environment ι) (t : ι → ℝ) : ℝ :=
  E.t0 + ∑ j, E.e j (t j)

def virtualValue {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (s : ℝ) : ℝ :=
  s - E.e i s - (1 - F E i s) / E.f i s

end MyersonAuction.Optimal
