import data.polynomial.basic
import ring_theory.non_zero_divisors
import ring_theory.nilpotent

open_locale polynomial

open polynomial

variables (R : Type) [comm_ring R] (P : R[X])

example (P ∉ non_zero_divisors R[X]) :
  ∃ (r : R), r ≠ 0 ∧ (C r) * P = 0 :=
begin
  induction h : P.nat_degree using nat.strong_induction_on with k hind generalizing P,
  
  dsimp at hind,
  
  by_cases hdeg : P.nat_degree = 0,
  {
    
    have INT_1 : ∃ (α : R), ¬ α = 0 ∧ ((C α)*P).nat_degree = k-1,
    {
      sorry
    },
    
    obtain ⟨α,b,ha⟩ := INT_1,  

    have INT_2 : ∃ (β : R), ¬ β = 0 ∧ ((C β)*((C α)*P)) = 0,   
    {
      sorry
    },

    obtain ⟨β,b,hb⟩ := INT_2,

    -- appliquer l'associativité et normalement c'est gagné
    -- mais problème pour montrer que alphabeta != 0

  },
  {
    --P.erase_lead
    sorry
  }

end

example (H : is_nilpotent P) : ∀ i, is_nilpotent (P.coeff i) :=
begin
  sorry
end
