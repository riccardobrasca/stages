import data.polynomial.erase_lead
import ring_theory.non_zero_divisors
import ring_theory.nilpotent

open_locale polynomial

open polynomial

variables (R : Type) [comm_ring R] (P : R[X])

lemma basique : (P ∉ non_zero_divisors R[X]) ↔ ∃ Q ≠ 0, P * Q = 0 :=
begin
  intro h,
  dsimp [mem_non_zero_divisors_iff] at h,
  simp at h,
  obtain ⟨Q,hq⟩ := h,
  use Q,
  split,
  {
    apply hq.2,
  },
  {
    cases hq with hq1 hq2,
    rw mul_comm at hq1,
    exact hq1,
  },
end

lemma foo (P ∉ non_zero_divisors R[X]) : P.erase_lead ∉ non_zero_divisors R[X] :=
begin
  sorry
end

example (P ∉ non_zero_divisors R[X]) :
  ∃ (r : R), r ≠ 0 ∧ (C r) * P = 0 :=
begin

  obtain ⟨Q,hq1,hq2⟩ := basique R P h,
  -- permet d'obtenir Q tel que PQ = 0

  by_cases Q.nat_degree ≥ 1,
  {
    -- pour ce cas il me faut supposer la minimalité de deg(Q) 
    -- mais je ne vois pas comment le faire de manière simple
    
    -- ensuite je pourrais effectuer un raisonnement par l'absurde
    -- et ça devrait suffire
    sorry
  },
  {
    simp at h,
    -- ici je voudrais pouvoir 'use' directement le terme constant de Q.
    -- il me faudrait une sorte de réciproque de C r
    sorry
  }

end

example (H : is_nilpotent P) : ∀ i, is_nilpotent (P.coeff i) :=
begin
  sorry
end
