import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

/-! # Combinatorial optimization problems and their decision problems

Karp & Papadimitriou, *On linear characterizations of combinatorial optimization problems*,
MIT/LCS/TM-154 (Feb. 1980), §2, pp. 3–4: Definition 1 (combinatorial optimization problems),
instances, and the decision problem `D(C)`.

Strings and tuples are written over the four-letter alphabet `BSym = {0, 1, −, #}` of the
published definition file `ProjSchedTW_Complexity_Encoding`; every integer is written in binary
(`encInt`), so the length of a code is the size of the tuple it encodes. -/

/-- The code of a string `z ∈ {0,1}*`: its bits (`false ↦ 0`, `true ↦ 1`), closed by `#`. -/
def encBits (z : List Bool) : List BSym :=
  z.map (fun b => if b then BSym.one else BSym.zero) ++ [BSym.sep]

/-- The code of an integer vector `v ∈ ℤᵐ`: its length `m` in binary, then each entry in binary. -/
def encVec {m : ℕ} (v : Fin m → ℤ) : List BSym :=
  encNat m ++ encInts (List.ofFn v)

/-- The code `⟨z, x⟩` of a string `z` and an integer vector `x`. -/
def encPair {m : ℕ} (z : List Bool) (x : Fin m → ℤ) : List BSym :=
  encBits z ++ encVec x

/-- The code `⟨z, v, a⟩` of a string `z`, an integer vector `v` and an integer `a`. It is used
both for the inputs `⟨z, c, k⟩` of the decision problem and for the triples `⟨z, f, g⟩` of a
facial description. -/
def encTriple {m : ℕ} (z : List Bool) (v : Fin m → ℤ) (a : ℤ) : List BSym :=
  encBits z ++ encVec v ++ encInt a

/-- **Definition 1** (pp. 3–4). A combinatorial optimization problem (c.o.p.) `C` is specified by
(i) a set `L ⊆ {0,1}*`; (ii) a function `n` from `L` into the nonnegative integers (its values
off `L` are irrelevant); (iii) for each `z ∈ L` a set `S(z)` of nonnegative integer vectors of
length `n(z)`; such that the three languages `L`, `{⟨z,y⟩ | |y| = n(z)}` and
`{⟨z,x⟩ | x ∈ S(z)}` are recognizable in polynomial time (Cook's class `P` over `BSym`). -/
structure COP where
  /-- The set `L ⊆ {0,1}*` of problem inputs. -/
  L : Set (List Bool)
  /-- The number of variables `n(z)` of the input `z`. -/
  n : List Bool → ℕ
  /-- The set `S(z)` of feasible solutions of the input `z`. -/
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  /-- `S(z) ⊆ (ℤ⁺)ⁿ⁽ᶻ⁾`: feasible solutions are nonnegative integer vectors. -/
  S_nonneg : ∀ z ∈ L, ∀ x ∈ S z, ∀ j, 0 ≤ x j
  /-- The language `L` is recognizable in polynomial time. -/
  L_poly : {w : List BSym | ∃ z ∈ L, w = encBits z} ∈ P BSym
  /-- The language `{⟨z,y⟩ | |y| = n(z)}` (with `z ∈ L`, `y ∈ {0,1}*`) is recognizable in
  polynomial time. -/
  len_poly : {w : List BSym | ∃ z ∈ L, ∃ y : List Bool, y.length = n z ∧
    w = encBits z ++ encBits y} ∈ P BSym
  /-- The language `{⟨z,x⟩ | x ∈ S(z)}` (with `z ∈ L`) is recognizable in polynomial time. -/
  S_poly : {w : List BSym | ∃ z ∈ L, ∃ x ∈ S z, w = encPair z x} ∈ P BSym

/-- The decision problem `D(C)` (p. 4): the codes of the triples `⟨z, c, k⟩` with `z ∈ L`,
`c ∈ ℤⁿ⁽ᶻ⁾`, `k ∈ ℤ` such that some `x ∈ S(z)` has `c · x ≥ k`. -/
def DLang (C : COP) : Lang BSym :=
  {w | ∃ z ∈ C.L, ∃ (c : Fin (C.n z) → ℤ) (k : ℤ),
    (∃ x ∈ C.S z, k ≤ c ⬝ᵥ x) ∧ w = encTriple z c k}

/-- The convex hull `CH(S(z)) ⊆ ℚⁿ⁽ᶻ⁾` of the feasible set (the paper's `R` is the rationals,
footnote p. 3). -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ ((fun x : Fin (C.n z) → ℤ => fun j => (x j : ℚ)) '' C.S z)

end KarpPapadimitriou.Facial
