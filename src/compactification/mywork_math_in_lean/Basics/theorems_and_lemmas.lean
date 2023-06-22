import analysis.special_functions.log.basic

variables a b c d e : ℝ
open real


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
  begin
    have h₄: a<c,
    by apply lt_of_le_of_lt h₀ h₁,
    
    have h₅: a<d,
    by apply lt_of_lt_of_le h₄ h₂,

    by exact lt_trans h₅ h₃,
  end


example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add_left,
  apply exp_le_exp.mpr,
  apply add_le_add_left h₀, 
end

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  {apply add_pos,
  apply zero_lt_one,
  apply exp_pos},
  have h₁ : 0 < 1 + exp b,
  {apply add_pos,
  apply zero_lt_one,
  apply exp_pos},
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add_left,
  apply exp_le_exp.mpr h,
end

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
  begin
  apply add_neg_le_add_neg_iff.mpr,
  apply add_le_add_left,
  apply exp_le_exp.mpr h,
  exact has_add.to_covariant_class_left ℝ,
  end


