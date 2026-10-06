import Mathlib

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colouring of one round (p. 9), with `true` = red and `false` = blue. Write the chosen
edge as `e = {u, w}` with `(u, w) = e.out`. The node `u` gets colour `b` and `w` gets colour
`!b` (so `b` is the fair coin deciding which endpoint is red), and every other node `x` gets the
independent fair colour `c x`. -/
noncomputable def roundColoring (e : Sym2 V) (b : Bool) (c : V → Bool) : V → Bool :=
  fun x => if x = e.out.1 then b else if x = e.out.2 then !b else c x

open Classical in
/-- The part created for the red node `x` (p. 9): the edges of the current edge set `E` that
are incident on `x` and have a blue endpoint, i.e. all red-blue edges incident on `x`. -/
noncomputable def redPart (E : Finset (Sym2 V)) (col : V → Bool) (x : V) : Finset (Sym2 V) :=
  E.filter fun e => x ∈ e ∧ ∃ y ∈ e, col y = false

open Classical in
/-- The parts created in one round: one part for each red node, empty parts dropped. -/
noncomputable def roundParts (E : Finset (Sym2 V)) (col : V → Bool) : Finset (Finset (Sym2 V)) :=
  ((Finset.univ.filter fun x => col x = true).image (redPart E col)).filter Finset.Nonempty

open Classical in
/-- The edges of the current edge set `E` with both endpoints blue: the edge set on which the
procedure recurses (p. 9). All other edges of `E` (red-red, and red-blue ones already placed in a
part) are discarded for good. -/
noncomputable def blueEdges (E : Finset (Sym2 V)) (col : V → Bool) : Finset (Sym2 V) :=
  E.filter fun e => ∀ y ∈ e, col y = false

/-- The non-loop edges of `E` (all of `E` when `E` is the edge set of a simple graph). -/
def properEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => ¬ e.IsDiag

theorem blueEdges_card_lt (E : Finset (Sym2 V)) (e : {e // e ∈ properEdges E}) (b : Bool)
    (c : V → Bool) : (blueEdges E (roundColoring e.1 b c)).card < E.card := by
  classical
  obtain ⟨e, he⟩ := e
  simp only [properEdges, Finset.mem_filter] at he
  obtain ⟨heE, hnd⟩ := he
  apply Finset.card_lt_card
  refine Finset.filter_ssubset.2 ⟨e, heE, ?_⟩
  have hne : e.out.1 ≠ e.out.2 := by
    intro h
    apply hnd
    rw [← Quot.out_eq e]
    exact (Sym2.mk_isDiag_iff).2 h
  intro hall
  have h1 := hall _ (Sym2.out_fst_mem e)
  have h2 := hall _ (Sym2.out_snd_mem e)
  simp only [roundColoring, if_neg (Ne.symm hne)] at h1 h2
  cases b <;> simp_all

/-- The random partition of Lemma 5.3 (p. 9), as a probability mass function on finite
families of parts. On the current edge set `E`: if `E` has no (non-loop) edge, return the empty
family. Otherwise pick an edge `e` of `E` uniformly at random, a fair coin `b` deciding which
endpoint of `e` is red, and independent fair colours `c` for all nodes; colour by
`roundColoring e b c`; output the parts of the red nodes, together with the parts produced by
running the procedure recursively on the blue-blue edges of `E`. -/
noncomputable def partitionPMF (E : Finset (Sym2 V)) : PMF (Finset (Finset (Sym2 V))) :=
  if h : (properEdges E).Nonempty then
    (PMF.uniformOfFinset (properEdges E).attach (by simpa using h)).bind fun e =>
      (PMF.uniformOfFintype Bool).bind fun b =>
        (PMF.uniformOfFintype (V → Bool)).bind fun c =>
          (partitionPMF (blueEdges E (roundColoring e.1 b c))).map fun Q =>
            roundParts E (roundColoring e.1 b c) ∪ Q
  else PMF.pure ∅
termination_by E.card
decreasing_by exact blueEdges_card_lt E e b c

end SecretaryWD.Graphic
