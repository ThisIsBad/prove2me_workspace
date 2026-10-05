import Mathlib

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 96, `ancestor`: the Boolean matrix is updated in place in
pivot, row, column order. -/
def algorithm96 {n : ℕ} (b : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  (List.finRange n).foldl (fun m i =>
    (List.finRange n).foldl (fun m j =>
      if m j i then
        (List.finRange n).foldl (fun m k =>
          if m i k then Function.update m j (Function.update (m j) k true)
          else m) m
      else m) m) b

end FloydAlgorithms.ShortestPath
