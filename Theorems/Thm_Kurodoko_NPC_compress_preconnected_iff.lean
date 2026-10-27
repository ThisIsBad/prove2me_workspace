import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Proof of Theorem 2, p. 695: the compression step for rule 3. For a set `B` of squares of the
board of width `w` and height `h`:
* if rows `r` and `r + 1` contain no black square, the white squares are connected iff they are
  connected on the board with the two rows merged (height `h − 1`, rows below `r` shifted up);
* the same for two adjacent columns `c`, `c + 1` (width `w − 1`);
* if no two adjacent rows are free of black squares then `h ≤ 2|B| + 1`, and likewise
  `w ≤ 2|B| + 1` for columns. -/
theorem compress_preconnected_iff (w h : ℕ) (B : Finset Cell) (hB : ∀ v ∈ B, OnBoard w h v) :
    (∀ r, r + 1 < h → (∀ v ∈ B, v.1 ≠ r ∧ v.1 ≠ r + 1) →
      (Rule3 w h B ↔
        Rule3 w (h - 1) (B.image fun v => if r < v.1 then (v.1 - 1, v.2) else v))) ∧
    (∀ c, c + 1 < w → (∀ v ∈ B, v.2 ≠ c ∧ v.2 ≠ c + 1) →
      (Rule3 w h B ↔
        Rule3 (w - 1) h (B.image fun v => if c < v.2 then (v.1, v.2 - 1) else v))) ∧
    ((∀ r, r + 1 < h → ∃ v ∈ B, v.1 = r ∨ v.1 = r + 1) → h ≤ 2 * B.card + 1) ∧
    ((∀ c, c + 1 < w → ∃ v ∈ B, v.2 = c ∨ v.2 = c + 1) → w ≤ 2 * B.card + 1) := by sorry

end Kurodoko.NPC

