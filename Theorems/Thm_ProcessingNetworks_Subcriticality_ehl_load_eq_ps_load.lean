import Mathlib

namespace ProcessingNetworks.Subcriticality

open Matrix

/-- Proposition 4.3, p.79 (PDF p.95): the load vector of the equivalent head-of-line (EHL) model
equals the load vector of the processor-sharing (PS) network it was derived from,

`ρ̃ = ρ`.

The two load vectors are the ones of Section 2.6, computed by (4.28) and (4.29):

`ρ̃ = Ã M̃ α̃`  where  `α̃ = (I − P̃′)⁻¹ λ̃`,     (4.28)
`ρ  = A M α`   where  `α  = (I − P′)⁻¹ λ`.      (4.29)

The book calls the proposition "obvious" in a sense, since `ρ_k` and `ρ̃_k` have the same
interpretation — the total service effort required from server `k` per time unit — and says its
"formal proof simply confirms that no mistake has been made in the development to this point".

**Formalization note.** The EHL construction of §4.4 refines each class `i` into the classes
`(i, s)` for `s` a service phase of `i`, the phase-type structure being Assumption 2.1. Its data
are carried here by the relations that define them from the PS data, not by their consequences:
external arrivals to a refined class are `λ̃_{(i,s)} = λ_i p^i_s`, capacity consumption is
inherited unchanged (`Ã_{k,(i,s)} = A_{k,i}`, since a refined class is served by the same server),
mean service times are per phase (`m̃_{(i,s)} = m^i_s`), and the class mean service time is the
expected total over the phase-type chain, `m_i = Σ_s ν^i_s m^i_s` with
`ν^i = (I − (P^i)′)⁻¹ p^i`. The total arrival rate vectors `α` and `α̃` are given by their own
defining equations (4.29) and (4.28); in particular `α̃` is **not** assumed to equal
`α_i ν^i`, which is the step the book's proof establishes. As the book states ("the substochastic
matrices `P¹, …, P^I` and `P` are all transient"), the routing matrix `P` and the phase-transition
matrices `P^i` are substochastic and transient (`Pⁿ → 0`), which is what makes the linear systems
(4.28), (4.29) and `ν^i = (I − (P^i)′)⁻¹ p^i` uniquely solvable. -/
theorem ehl_load_eq_ps_load {I K : ℕ} (S : Fin I → ℕ)
    -- PS network data (Section 2.6)
    (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (A : Matrix (Fin K) (Fin I) ℝ)
    (m : Fin I → ℝ) (alpha : Fin I → ℝ)
    -- the phase-type structure of each class's service time (Assumption 2.1)
    (pinit : (i : Fin I) → Fin (S i) → ℝ)
    (Pph : (i : Fin I) → Matrix (Fin (S i)) (Fin (S i)) ℝ)
    (mph : (i : Fin I) → Fin (S i) → ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (hPph_nonneg : ∀ i s s', 0 ≤ Pph i s s') (hPph_rowsum : ∀ i s, ∑ s', Pph i s s' ≤ 1)
    (hPph_transient : ∀ i s s', Filter.Tendsto (fun n => ((Pph i) ^ n) s s') Filter.atTop (nhds 0))
    (nu : (i : Fin I) → Fin (S i) → ℝ)
    (hnu : ∀ i, ((1 : Matrix (Fin (S i)) (Fin (S i)) ℝ) - (Pph i).transpose).mulVec (nu i)
      = pinit i)
    (hm : ∀ i, m i = ∑ s, nu i s * mph i s)
    -- the EHL data, defined from the PS data by the construction of §4.4
    (ltil : ((i : Fin I) × Fin (S i)) → ℝ)
    (Ptil : Matrix ((i : Fin I) × Fin (S i)) ((i : Fin I) × Fin (S i)) ℝ)
    (atil : ((i : Fin I) × Fin (S i)) → ℝ)
    (hltil : ∀ (i : Fin I) (s : Fin (S i)), ltil ⟨i, s⟩ = lam i * pinit i s)
    (hPtil_same : ∀ (i : Fin I) (s s' : Fin (S i)), Ptil ⟨i, s⟩ ⟨i, s'⟩ = Pph i s s')
    (hPtil_diff : ∀ (i j : Fin I), i ≠ j → ∀ (s : Fin (S i)) (s' : Fin (S j)),
      Ptil ⟨i, s⟩ ⟨j, s'⟩ = (1 - ∑ s'' : Fin (S i), Pph i s s'') * P i j * pinit j s')
    -- (4.28) and (4.29): the two total arrival rate vectors
    (hatil : ((1 : Matrix ((i : Fin I) × Fin (S i)) ((i : Fin I) × Fin (S i)) ℝ)
      - Ptil.transpose).mulVec atil = ltil)
    (halpha : ((1 : Matrix (Fin I) (Fin I) ℝ) - P.transpose).mulVec alpha = lam) :
    -- ρ̃ = ρ
    (fun k => ∑ c : (i : Fin I) × Fin (S i), A k c.1 * mph c.1 c.2 * atil c)
      = fun k => ∑ i, A k i * m i * alpha i := by sorry

end ProcessingNetworks.Subcriticality
