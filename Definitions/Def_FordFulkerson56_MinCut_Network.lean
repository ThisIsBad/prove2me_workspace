import Mathlib

namespace FordFulkerson56.MinCut

/-- A network in the sense of Ford and Fulkerson (1956), §1, p. 399: a finite graph whose arcs form a
type `E` (so two arcs may have the same end vertices), each arc `e` having two distinct end vertices
`tail e` and `head e` (the names are labels only: arcs are undirected), a distinguished source and sink,
which are two distinct vertices, and a positive capacity on every arc. -/
structure Network (V E : Type*) where
  tail : E → V
  head : E → V
  tail_ne_head : ∀ e, tail e ≠ head e
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  cap : E → ℝ
  cap_pos : ∀ e, 0 < cap e

end FordFulkerson56.MinCut
