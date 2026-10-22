import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model

namespace ZipkinLostSales.Variability

open MeasureTheory

/-!
# Zipkin (2008), §2–§3: the lost-sales recursion in the transformed state `v`, with the demand
law as a parameter

Conventions (Zipkin, *On the Structure of Lost-Sales Inventory Models*, Oper. Res. 56 (2008),
pp. 937–939):

* `L : ℕ` is the lead time; states are `v : Fin L → ℝ`, indexed `0, …, L-1` as in the paper, and
  `vext v l` extends `v` by the paper's convention `v_L = 0` (and `0` beyond).
* Costs: `c` (procurement), `hh` (= ĥ, holding), `p` (lost-sales penalty), `γ` (discount factor).
* `μ : Measure ℝ` is the law of one period's demand `d` (data are stationary and the demands are
  independent, so one law serves every period). Every object below that involves an expectation
  takes `μ` as an explicit argument, so that the paper's `f̄_t(v; φ)` of §5 is `fbar … (μ φ) k v`.
* Time is indexed by the number of periods to go `k : ℕ`: `fbar … 0 = 0` is (2), and `gbar … k`
  is the paper's `ḡ_t` for the period `t` with `k + 1` periods to go, whose continuation is
  `fbar … k` (the paper's `f̄_{t+1}`); `fbar … (k+1) v = ⨅_{ζ ≤ 0} ZipkinLostSales.LNatural.gbar … k v ζ` is (1). By
  stationarity "for all t" is "for all k".
* The paper's "min" is the infimum `⨅ ζ : Set.Iic (0:ℝ)`. Under nonnegative costs and nonnegative
  demand every term of `gbar` is `≥ 0`, so the infimum is over a set bounded below and is not
  Lean's junk value; this is not proved here.
-/

/-- `fbar … (k+1)` unfolds to the infimum of `gbar … k` over `ζ ≤ 0` (definitional). -/
theorem fbar_succ {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (k : ℕ) (v : Fin L → ℝ) :
    ZipkinLostSales.LNatural.fbar c hh p γ μ (k + 1) v = ⨅ ζ : Set.Iic (0 : ℝ), ZipkinLostSales.LNatural.gbar c hh p γ μ k v ζ := rfl

/-- `fbar … 0 = 0`, condition (2) (definitional). -/
theorem fbar_zero {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (v : Fin L → ℝ) :
    ZipkinLostSales.LNatural.fbar c hh p γ μ 0 v = 0 := rfl

end ZipkinLostSales.Variability
