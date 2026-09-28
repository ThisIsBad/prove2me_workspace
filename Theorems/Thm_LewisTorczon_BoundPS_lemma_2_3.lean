import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Lemma 2.3** (Lemma 3.6 of Torczon 1997), p. 5: if the columns of the generating matrices are
uniformly bounded in norm, there is `ψ_* > 0`, independent of `k`, with `Δ_k ≥ ψ_* ‖s_k^i‖` for
every trial step `s_k^i = Δ_k B c_k^i`. -/
theorem lemma_2_3 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (hbdd : BoundedCols R) :
    ∃ ψ : ℝ, 0 < ψ ∧ ∀ k, ∀ c ∈ cols R k, ψ * ‖stepOf P (R.Δ k) c‖ ≤ R.Δ k := by sorry

end LewisTorczon.BoundPS
