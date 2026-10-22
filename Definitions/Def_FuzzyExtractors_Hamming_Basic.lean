import Mathlib

namespace FuzzyExtractors.Hamming

open scoped ENNReal

noncomputable section

/-! ### Shared model (§2.3–§3.2, pp. 8–13) -/

/-- Min-entropy H∞(A) = −log max_a Pr[A = a] (§2.3, p. 8). -/
def minEntropy {α : Type*} (A : PMF α) : ℝ :=
  -Real.logb 2 (⨆ a, A a).toReal

/-- Average min-entropy H̃∞(A | B) = −log E_{b←B}[max_a Pr[A = a | B = b]] (§2.4, p. 9),
written in the equivalent joint form −log Σ_b max_a Pr[A = a ∧ B = b]. -/
def avgMinEntropy {α β : Type*} (AB : PMF (α × β)) : ℝ :=
  -Real.logb 2 (∑' b, ⨆ a, AB (a, b)).toReal

/-- Statistical distance SD(A, B) = ½ Σ_v |Pr(A = v) − Pr(B = v)| (§2.3, p. 8). -/
def statDist {α : Type*} (A B : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑' v, |(A v).toReal - (B v).toReal|

/-- U_ℓ, the uniform distribution on ℓ-bit strings (§2, p. 7). -/
def uniformBits (ℓ : ℕ) : PMF (Fin ℓ → Bool) := PMF.uniformOfFintype _

/-- Correctness of a secure sketch (Definition 3, item 2). -/
def SketchCorrect {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  ∀ w w', dis w w' ≤ t → ∀ s ∈ (SS w).support, Rec w' s = PMF.pure w

/-- The joint law of (W, SS(W)). -/
def withSketch {M S : Type} (SS : M → PMF S) (W : PMF M) : PMF (M × S) :=
  W.bind fun w => (SS w).map fun s => (w, s)

/-- The joint law of (W, (SS(W), I)) from the joint law of (W, I). -/
def withSketchAux {M S ι : Type} (SS : M → PMF S) (WI : PMF (M × ι)) : PMF (M × (S × ι)) :=
  WI.bind fun p => (SS p.1).map fun s => (p.1, (s, p.2))

/-- An (M, m, m̃, t)-secure sketch (Definition 3). -/
def IsSecureSketch {M S : Type} (dis : M → M → ℕ) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  SketchCorrect dis t SS Rec ∧
    ∀ W : PMF M, m ≤ minEntropy W → m' ≤ avgMinEntropy (withSketch SS W)

/-- An average-case (M, m, m̃, t)-secure sketch (Definition 4). -/
def IsAvgSecureSketch {M S : Type} (dis : M → M → ℕ) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  SketchCorrect dis t SS Rec ∧
    ∀ (ι : Type) (WI : PMF (M × ι)), m ≤ avgMinEntropy WI →
      m' ≤ avgMinEntropy (withSketchAux SS WI)

/-- Correctness of a fuzzy extractor (Definition 5, item 2). -/
def ExtractorCorrect {M P : Type} {ℓ : ℕ} (dis : M → M → ℕ) (t : ℕ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ∀ w w', dis w w' ≤ t → ∀ rp ∈ (Gen w).support, Rep w' rp.2 = PMF.pure rp.1

/-- An (M, m, ℓ, t, ε)-fuzzy extractor (Definition 5): SD((R, P), (U_ℓ, P)) ≤ ε. -/
def IsFuzzyExtractor {M P : Type} (dis : M → M → ℕ) (m : ℝ) (ℓ t : ℕ) (ε : ℝ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ExtractorCorrect dis t Gen Rep ∧
    ∀ W : PMF M, m ≤ minEntropy W →
      statDist (W.bind Gen)
        ((W.bind Gen).bind fun rp => (uniformBits ℓ).map fun u => (u, rp.2)) ≤ ε

/-- The average-case variant (p. 13): if H̃∞(W | I) ≥ m then SD((R, P, I), (U_ℓ, P, I)) ≤ ε. -/
def IsAvgFuzzyExtractor {M P : Type} (dis : M → M → ℕ) (m : ℝ) (ℓ t : ℕ) (ε : ℝ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ExtractorCorrect dis t Gen Rep ∧
    ∀ (ι : Type) (WI : PMF (M × ι)), m ≤ avgMinEntropy WI →
      statDist (WI.bind fun p => (Gen p.1).map fun rp => (rp.1, rp.2, p.2))
        ((WI.bind fun p => (Gen p.1).map fun rp => (rp.1, rp.2, p.2)).bind
          fun x => (uniformBits ℓ).map fun u => (u, x.2.1, x.2.2)) ≤ ε

/-! ### Strong extractors and universal hashing (§2.3–§2.5, pp. 8–10) -/

/-- A family `{H_x : α → {0,1}^ℓ}_{x ∈ X}` is universal (Lemma 2.1, p. 9):
for all `a ≠ b`, `Pr_{x ∈ X}[H_x(a) = H_x(b)] = 2^{−ℓ}`, `x` uniform on `X`. -/
def IsUniversal {α X : Type} [Fintype X] {ℓ : ℕ} (H : X → α → (Fin ℓ → Bool)) : Prop :=
  ∀ a b, a ≠ b →
    ((Finset.univ.filter fun x => H x a = H x b).card : ℝ) / Fintype.card X = (2 : ℝ) ^ (-(ℓ : ℤ))

/-- The joint law of (Ext(W; X), X), with the seed X uniform on `X` and independent of W. -/
def extractLaw {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (Ext : α → X → (Fin ℓ → Bool)) (W : PMF α) : PMF ((Fin ℓ → Bool) × X) :=
  W.bind fun w => (PMF.uniformOfFintype X).map fun x => (Ext w x, x)

/-- The joint law of (Ext(W; X), X, I) from the joint law of (W, I), with X uniform and
independent of (W, I). -/
def extractLawAux {α X ι : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (Ext : α → X → (Fin ℓ → Bool)) (WI : PMF (α × ι)) : PMF ((Fin ℓ → Bool) × X × ι) :=
  WI.bind fun p => (PMF.uniformOfFintype X).map fun x => (Ext p.1 x, x, p.2)

/-- An (n, m, ℓ, ε)-strong extractor (Definition 1, p. 8), for a finite input set `α` and a
finite nonempty seed set `X`: for every W with H∞(W) ≥ m, SD((Ext(W; X), X), (U_ℓ, X)) ≤ ε. -/
def IsStrongExtractor {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ} (m ε : ℝ)
    (Ext : α → X → (Fin ℓ → Bool)) : Prop :=
  ∀ W : PMF α, m ≤ minEntropy W →
    statDist (extractLaw Ext W)
      ((extractLaw Ext W).bind fun y => (uniformBits ℓ).map fun u => (u, y.2)) ≤ ε

/-- An average-case (n, m, ℓ, ε)-strong extractor (Definition 2, p. 10): for every pair (W, I)
with H̃∞(W | I) ≥ m, SD((Ext(W; X), X, I), (U_ℓ, X, I)) ≤ ε. -/
def IsAvgStrongExtractor {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ} (m ε : ℝ)
    (Ext : α → X → (Fin ℓ → Bool)) : Prop :=
  ∀ (ι : Type) (WI : PMF (α × ι)), m ≤ avgMinEntropy WI →
    statDist (extractLawAux Ext WI)
      ((extractLawAux Ext WI).bind fun y => (uniformBits ℓ).map fun u => (u, y.2.1, y.2.2)) ≤ ε

/-! ### Codes (§2.2, pp. 7–8) -/

/-- An (M, K, t)-code with K = |C| (§2.2, p. 8): every w ∈ M has at most one codeword c with
dis(w, c) ≤ t. -/
def IsCode {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ) : Prop :=
  ∀ w, ∀ c ∈ C, ∀ c' ∈ C, dis w c ≤ t → dis w c' ≤ t → c = c'

/-- The code C ⊆ 𝓕^n has minimum Hamming distance at least d (§2.2, p. 7). -/
def MinDistGe {F : Type} [DecidableEq F] {n : ℕ} (C : Finset (Fin n → F)) (d : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c'

/-- A codeword within distance t of y, if one exists (otherwise y itself, with no guarantee).
For an (M, K, t)-code it is the unique such codeword, hence the closest codeword. -/
def decodeWithin {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ) (y : M) : M :=
  open Classical in
  if h : ∃ c ∈ C, dis y c ≤ t then h.choose else y

/-! ### Construction 1: the sketch for transitive metric spaces (§4.2, p. 14) -/

/-- Construction 1, SS: pick b ∈ C uniformly, then π ∈ Π uniformly among those with
π(w) = b, and output π. Transitivity makes the second set nonempty. -/
def transSS {M Pm : Type} [Fintype Pm] [DecidableEq M] (C : Finset M) (hC : C.Nonempty)
    (act : Pm → M ≃ M) (htrans : ∀ a b, ∃ π, act π a = b) (w : M) : PMF Pm :=
  (PMF.uniformOfFinset C hC).bind fun b =>
    PMF.uniformOfFinset (Finset.univ.filter fun π => act π w = b)
      (by
        obtain ⟨π, hπ⟩ := htrans w b
        exact ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ π, hπ⟩⟩)

/-- Construction 1, Rec: decode π(w′) to a codeword b′ and output π⁻¹(b′). -/
def transRec {M Pm : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ)
    (act : Pm → M ≃ M) (w' : M) (π : Pm) : PMF M :=
  PMF.pure ((act π).symm (decodeWithin dis C t (act π w')))

/-! ### Constructions 2 and 3: code-offset and syndrome sketches (§5, p. 16) -/

/-- Construction 2, SS: pick c ∈ C uniformly and output w − c. -/
def codeOffsetSS {F : Type} [AddCommGroup F] {n : ℕ} (C : Finset (Fin n → F))
    (hC : C.Nonempty) (w : Fin n → F) : PMF (Fin n → F) :=
  (PMF.uniformOfFinset C hC).map fun c => w - c

/-- Construction 2, Rec: decode c′ = w′ − s to c and output c + s. -/
def codeOffsetRec {F : Type} [AddCommGroup F] [DecidableEq F] {n : ℕ}
    (C : Finset (Fin n → F)) (t : ℕ) (w' s : Fin n → F) : PMF (Fin n → F) :=
  PMF.pure (decodeWithin hammingDist C t (w' - s) + s)

/-- Construction 3, SS: output the syndrome syn(w) (deterministic). -/
def syndromeSS {F : Type} [Field F] {n r : ℕ} (syn : (Fin n → F) →ₗ[F] (Fin r → F))
    (w : Fin n → F) : PMF (Fin r → F) :=
  PMF.pure (syn w)

/-- Construction 3, Rec: find e of Hamming weight ≤ t with syn(e) = syn(w′) − s (if one
exists; otherwise e = 0, with no guarantee) and output w′ − e. -/
def syndromeRec {F : Type} [Field F] [DecidableEq F] {n r : ℕ}
    (syn : (Fin n → F) →ₗ[F] (Fin r → F)) (t : ℕ) (w' : Fin n → F) (s : Fin r → F) :
    PMF (Fin n → F) :=
  open Classical in
  PMF.pure (w' - if h : ∃ e : Fin n → F, hammingNorm e ≤ t ∧ syn e = syn w' - s
    then h.choose else 0)

/-! ### The construction of Lemma 4.1 (§4.1, p. 13) -/

/-- Lemma 4.1, Gen(w; r, x): P = (SS(w; r), x), R = Ext(w; x), output (R, P);
x uniform on the seed set X, independent of the sketch's coins. -/
def sketchExtGen {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (w : M) : PMF ((Fin ℓ → Bool) × (S × X)) :=
  (SS w).bind fun s => (PMF.uniformOfFintype X).map fun x => (Ext w x, (s, x))

/-- Lemma 4.1, Rep(w′, (s, x)): recover w = Rec(w′, s) and output Ext(w; x). -/
def sketchExtRep {M S X : Type} {ℓ : ℕ}
    (Rec : M → S → PMF M) (Ext : M → X → (Fin ℓ → Bool)) (w' : M) (p : S × X) :
    PMF (Fin ℓ → Bool) :=
  (Rec w' p.1).map fun w => Ext w p.2

end

end FuzzyExtractors.Hamming
