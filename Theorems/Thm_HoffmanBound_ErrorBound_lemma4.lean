import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

/-- Hoffman 1952, p. 264, Lemma 4. With `M = rowsOn A S` and `E` as in Lemma 3, the cone spanned by
the row vectors of `M` with the origin deleted equals `E`. -/
theorem lemma4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    conePrime A S = setE A S := by sorry

end HoffmanBound.ErrorBound

