import Definitions.Def_InventoryControl_newsboy

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- The steady-state inventory position of a continuous review `(R, Q)` policy under continuous
demand: uniform on `[R, R + Q]`. Axsäter, *Inventory Control*, Sect. 5.3.1 p. 75. -/
noncomputable def rqPosition (R Q : ℝ) : Measure ℝ := volume[|Set.Icc R (R + Q)]

/-- The law of the inventory level `IL = IP - D(L)`, Eq. (5.35): the inventory position is
uniform on `[R, R + Q]` and the lead-time demand is normal with mean `m` and standard deviation
`s`, the two being independent. Axsäter, *Inventory Control*, Sects. 5.3.2 and 5.3.4. -/
noncomputable def rqLevel (R Q m s : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 - p.2) ((rqPosition R Q).prod (newsboyDemand m s))

/-- The distribution function `F(x) = P(IL ≤ x)` of the inventory level, Eq. (5.39). -/
noncomputable def rqCDF (R Q m s x : ℝ) : ℝ := (rqLevel R Q m s).real (Set.Iic x)

/-- The ready rate `S₃ = P(IL > 0)`, Eq. (5.50); equal to the fill rate `S₂` for continuous
demand, Sect. 5.7.2. -/
noncomputable def rqReadyRate (R Q m s : ℝ) : ℝ := (rqLevel R Q m s).real (Set.Ioi 0)

/-- `E(B)`: the expected backordered quantity covered by one batch, Sect. 5.8 p. 83.  With
lead-time demand `u`, `B = 0` if `u ≤ R`, `B = u - R` if `R < u ≤ R + Q`, and `B = Q` if
`u > R + Q`. -/
noncomputable def rqBatchBackorders (R Q m s : ℝ) : ℝ :=
  ∫ u, min (max (u - R) 0) Q ∂(newsboyDemand m s)

/-- The second loss function `H(x) = ∫_x^∞ G(v) dv`, Eq. (5.64). -/
noncomputable def normalLossH (x : ℝ) : ℝ := ∫ v in Set.Ioi x, normalLoss v

/-- The expected holding-plus-backorder cost rate `h E(IL)⁺ + b₁ E(IL)⁻`, Eq. (5.56) and
(5.62). -/
noncomputable def rqCost (h b1 R Q m s : ℝ) : ℝ :=
  ∫ x, (h * max x 0 + b1 * max (-x) 0) ∂(rqLevel R Q m s)

lemma isProbabilityMeasure_rqPosition (R Q : ℝ) (hQ : 0 < Q) :
    IsProbabilityMeasure (rqPosition R Q) := by
  unfold rqPosition
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;>
    simp [Real.volume_Icc, hQ]

lemma isProbabilityMeasure_rqLevel (R Q m s : ℝ) (hQ : 0 < Q) :
    IsProbabilityMeasure (rqLevel R Q m s) := by
  have := isProbabilityMeasure_rqPosition R Q hQ
  unfold rqLevel
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end InventoryControl
