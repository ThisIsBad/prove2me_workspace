import Definitions.Def_SupplyChainTheory_multiechelon


namespace SupplyChainTheory

/-- Snyder & Shen, *Fundamentals of Supply Chain Theory*, 2nd ed., p. 201, Theorem 6.4
(Shang & Song 2003): in the serial system of §6.2 with echelon holding costs `h_j > 0`, stockout
cost `p > 0` and **nonnegative** lead-time demands `D_j` of finite mean, with `S*` the
sequentially optimal vector of Theorem 6.3 and `gˡ_j`, `gᵘ_j` the newsvendor-type bounding
functions of p. 200: (a) `gˡ_j(y) ≤ g_j(y | S*) ≤ gᵘ_j(y)` for every `y`, and (b) a minimizer
`Sˡ_j` of `gᵘ_j` and a minimizer `Sᵘ_j` of `gˡ_j` bracket `S*_j`.

Corrected version: the demands are nonnegative random variables (`D_j([0, ∞)^c) = 0`), the
standing convention of the inventory models of the book; the retired statement allowed demand
laws with negative values, under which the pipeline-stock term of `gᵘ_j` turns negative and (a)
fails. -/
theorem shang_song_bounds_v2 (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (∀ y, ssLower N h p D j y ≤ csG N h p D Sstar j y
        ∧ csG N h p D Sstar j y ≤ ssUpper N h p D j y)
      ∧ ∃ Sl Su : ℝ, IsMinOn (ssUpper N h p D j) Set.univ Sl
          ∧ IsMinOn (ssLower N h p D j) Set.univ Su ∧ Sl ≤ Sstar j ∧ Sstar j ≤ Su := by sorry

end SupplyChainTheory

