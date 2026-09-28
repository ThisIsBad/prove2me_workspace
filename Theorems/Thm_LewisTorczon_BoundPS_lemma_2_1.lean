import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Lemma 2.1** (Lemma 3.1 of Torczon 1997), p. 4: there is `ζ_* > 0`, independent of `k`, with
`‖s_k^i‖ ≥ ζ_* Δ_k` for every nonzero trial step `s_k^i = Δ_k B c_k^i` of a generalized pattern
search run. -/
theorem lemma_2_1 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ k, ∀ c ∈ cols R k,
      stepOf P (R.Δ k) c ≠ 0 → ζ * R.Δ k ≤ ‖stepOf P (R.Δ k) c‖ := by sorry

end LewisTorczon.BoundPS
