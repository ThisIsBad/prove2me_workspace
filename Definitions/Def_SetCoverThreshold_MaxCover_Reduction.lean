import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover

/-- The **explicit partition system of §5** (p. 649): the points are the vectors
`x : ι → Fin k` (so there are `k^{|ι|}` of them), and the partition with index `i : ι` splits
them into `k` disjoint subsets according to the value `x i` of the `i`th coordinate. Point `x`
lies in subset `cubeSystem k ι x i` of partition `i`. -/
def cubeSystem (k : ℕ) (ι : Type) : (ι → Fin k) → ι → Fin k := fun x i => x i

open Classical in
/-- The questions prover `i` may receive: the image of the random strings under `question`. -/
noncomputable def possibleQuestions (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (i : Fin k) : Finset (Question φ ℓ) :=
  Finset.univ.image (fun r => question φ code r i)

/-- The index `(q, a, i)` of a set `S_(q,a,i)` of the reduction (p. 645): a prover `i`, a
question `q` that prover `i` may receive, and a canonical answer `a` to it. -/
abbrev SetIdx (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : Type :=
  Σ i : Fin k, Σ q : possibleQuestions φ code i, Answer φ q.1

/-- `kQ`: the total number of (prover, question) pairs, i.e. `k` times the number `Q` of possible
questions to a single prover when that number is the same for all provers. -/
noncomputable def coverBudget (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : ℕ :=
  ∑ i, (possibleQuestions φ code i).card

open Classical in
/-- **The set `S_(q,a,i)` of the reduction of §4** (p. 645), for a partition system on the
points `B` whose partitions are labelled by the `ℓ`-bit strings and whose parts are labelled by
the provers (`part b p` is the part of partition `p` containing the point `b`). The points of the
instance are the pairs `(r, b)` (one copy of the partition system for each random string `r`), and
`S_(q,a,i)` contains the point `(r, b)` iff prover `i` receives `q` on `r` and `b` lies in the
`i`th subset of the partition whose label is the assignment `a_r` that `a` induces on the
distinguished variables of `r`. -/
noncomputable def reductionSet (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    {B : Type} [Fintype B] (part : B → (Fin ℓ → Bool) → Fin k) (s : SetIdx φ code) :
    Finset (RandString φ ℓ × B) :=
  Finset.univ.filter (fun x =>
    question φ code x.1 s.1 = s.2.1.1 ∧ part x.2 (answerBits (fun j => (x.1 j).2) s.2.2) = s.1)

open Classical in
/-- The points covered by a collection `C` of sets of the §5 instance: the reduction of §4 with
the explicit partition system `cubeSystem k (Fin ℓ → Bool)` (with `m = k^L` points, `L = 2^ℓ`)
in every copy. -/
noncomputable def coveredMaxCover (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) : Finset (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) :=
  C.biUnion (reductionSet φ code (cubeSystem k (Fin ℓ → Bool)))

open Classical in
/-- `w_r`: the number of sets of the collection `C` that participate in covering points of the
partition system of `r`, i.e. the sets `S_(q,a,i) ∈ C` with `(q, i) ∈ r`. -/
noncomputable def setWeight (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ) : ℕ :=
  (C.filter (fun s => s.2.1.1 = question φ code r s.1)).card

/-- **Good random strings in §5** (p. 649): `r` is good if `w_r ≤ 3k/ε` and the sets of `C`
participating in covering points of the partition system of `r` contain two sets from the same
partition, i.e. two sets `S_(q,a,i)`, `S_(q',a',i')` with `(q,i), (q',i') ∈ r`, `i ≠ i'`, whose
answers induce the same label `a_r = a'_r`. -/
def IsGood (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (ε : ℝ)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ) : Prop :=
  (setWeight φ code C r : ℝ) ≤ 3 * k / ε ∧
    ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧ s.2.1.1 = question φ code r s.1 ∧
      s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2

open Classical in
/-- The number of good random strings. -/
noncomputable def goodCount (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (ε : ℝ)
    (C : Finset (SetIdx φ code)) : ℕ :=
  (Finset.univ.filter (IsGood φ code ε C)).card

end SetCoverThreshold.MaxCover
