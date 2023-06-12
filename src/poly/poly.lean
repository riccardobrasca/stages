import data.polynomial.basic
import ring_theory.non_zero_divisors
import ring_theory.nilpotent

open_locale polynomial

open polynomial

variables (R : Type) [comm_ring R] (P : R[X])

example (P ∉ non_zero_divisors R[X]) :
  ∃ (r : R), r ≠ 0 ∧ (C r) * P = 0 :=
begin
  sorry
end

example (H : is_nilpotent P) : ∀ i, is_nilpotent (P.coeff i) :=
begin
  sorry
end
