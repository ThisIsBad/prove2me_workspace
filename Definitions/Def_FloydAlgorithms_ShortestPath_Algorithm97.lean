import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network

namespace FloydAlgorithms.ShortestPath

/-- The column loop of Algorithm 97. The entry `m j i` is re-read for every
column, while the outer row guard is evaluated once. -/
noncomputable def rowSweep {n : ℕ} (i j : Fin n) (m : LengthMatrix n) : LengthMatrix n :=
  if m j i < ⊤ then
    (List.finRange n).foldl (fun m k =>
      if m i k < ⊤ then
        let s := m j i + m i k
        if s < m j k then Function.update m j (Function.update (m j) k s)
        else m
      else m) m
  else m

/-- Algorithm 97, `shortest path`, preserving the printed in-place loop order. -/
noncomputable def algorithm97 {n : ℕ} (w : LengthMatrix n) : LengthMatrix n :=
  (List.finRange n).foldl (fun m i =>
    (List.finRange n).foldl (fun m j => rowSweep i j m) m) w

end FloydAlgorithms.ShortestPath
