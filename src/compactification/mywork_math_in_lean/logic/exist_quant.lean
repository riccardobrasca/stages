import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

theorem fn_lb_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
intro x,
apply add_le_add,
apply hfa,
apply hgb,
end

section
variables {f g : ℝ → ℝ}

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
cases lbf with a lbfa,
cases lbg with b lbgb,
use a+b,
apply fn_lb_add lbfa lbgb,
end

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
cases ubf with a ubfa,
use c*a,
intros x,
apply mul_le_mul_of_nonneg_left,
apply ubfa,
apply h,
end

end


section
variables {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  rcases divab with ⟨n,rfl⟩,
  rcases divbc with ⟨m,rfl⟩,
  use n*m,
  ring,
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
rcases divab with ⟨n,rfl⟩,
rcases divac with ⟨m,rfl⟩,
use n+m,
ring,
end

end

section
open function

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
intros y,
use y/c,
dsimp,
apply mul_div_cancel' y h,
end

end

section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
intros y,
dsimp,
rcases surjg y with ⟨b,h1⟩,
rcases surjf b with ⟨a,h2⟩,
use a,
rw [h2,h1],
end

end