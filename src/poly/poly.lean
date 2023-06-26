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

/-- This is the set of polynomial `Q` such that `P * Q = 0` -/
def annihilator {R : Type*} [comm_ring R] (P : R[X]) := {Q : R[X] | P * Q = 0}

theorem nonvide (P ∉ non_zero_divisors R[X]) : (annihilator P).nonempty := sorry

/-- This is the image, via `nat_degree`, of `(annihilator P)`. -/
def annihilator_deg {R : Type*} [comm_ring R] (P : R[X]) := (λ Q : R[X], nat_degree Q)'' (annihilator P)

/-- `annihilator_deg` is nonempty if `P ∉ non_zero_divisors R[X]` (since `annihilator_deg P` is not empty). -/
theorem nonvide_image {R : Type*} [comm_ring R] {P : R[X]} (hP : P ∉ non_zero_divisors R[X]) : (annihilator_deg P).nonempty := sorry

/-- This means in practice that `annihilator_deg P` has a minimum. It is a mathlib stuff, every non empty `set ℕ ` is well founded. It doesn't matter for you what it means. -/
theorem bien_fondee {R : Type*} [comm_ring R] {P : R[X]} (hP : P ∉ non_zero_divisors R[X]) : (annihilator_deg P).is_wf := sorry


/-- This is the mininum of `nonvide_image`. Forget about `noncomputalbe`. -/
noncomputable
def min_deg (hP : P ∉ non_zero_divisors R[X]) := set.is_wf.min (bien_fondee hP) (nonvide_image hP)

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
