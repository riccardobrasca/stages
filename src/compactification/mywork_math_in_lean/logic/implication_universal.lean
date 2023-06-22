import data.real.basic


lemma my_lemma4 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
  abs (x * y) = abs x * abs y : by apply abs_mul
    ... ≤ abs x * ε             :
    begin
      apply mul_le_mul_of_nonneg_left,
      apply le_of_lt ylt,
      apply abs_nonneg,
    end    
    ... < 1 * ε                 :
    begin
      apply mul_lt_mul_of_pos_right,
      {apply lt_of_lt_of_le xlt ele1,},
      apply epos,
    end
    ... = ε                     : by apply one_mul,
end


def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

section
  variables (f g : ℝ → ℝ) (a b : ℝ)

  example (hfa : fn_lb f a) (hgb : fn_lb g b) :
    fn_lb (λ x, f x + g x) (a + b) :=
    begin
    intro x,
    dsimp,
    apply add_le_add,
    apply hfa,
    apply hgb,
    end
    
  example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
    fn_lb (λ x, f x * g x) 0 :=
    begin
    intro x,
    dsimp,
    apply mul_nonneg,
    apply nnf,
    apply nng,
    end

  example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
  begin
  intro x,
  dsimp,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna,
  end
end

section
  variables (f g : ℝ → ℝ)
  example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
  λ x y xley, mul_le_mul_of_nonneg_left (mf xley) nnc

  example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
  λ x y xley, (mf(mg xley))

  def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
  def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

  example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
  begin
    intro x,
    calc
      (λ x, f x + g x) x = f x + g x       : rfl
                      ... = f (-x) + g (-x) : by rw [ef, eg]
  end

  example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
    begin
    intro x,
    calc 
    (λ x,f(x)*g(x))(x)=f(x)*g(x):rfl
    ...= (-f(-x))*(-g(-x)): by rw [of, og]
    ...= f(-x)*g(-x): by apply neg_mul_neg,
    end

  example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
    begin
    intro x,
    calc
    (λ x, f x * g x)x=f x*g x : rfl
    ...= f(-x)*(-g(-x)) : by rw [ef, og]
    ...= -(f (-x) * g (-x)): by apply mul_neg,
    end

  example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
  by {intro x, dsimp, rw [og, ←ef]}
  
end

section
variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
by {intros a b x xr, apply b, apply a, apply xr}

end

section

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
by {intros x xs, apply le_trans, apply h, apply xs, apply h'}

end

section
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
intros x y h0,
exact (mul_right_inj' h).mp h0,
end

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
begin
intros x y h,
apply injf,
apply injg,
apply h,
end

end