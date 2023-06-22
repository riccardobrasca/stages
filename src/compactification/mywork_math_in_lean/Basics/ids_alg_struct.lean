

import algebra.ring.defs

section
variables (R : Type*) [ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end



namespace my_ring

variables {R:Type*} [ring R]

theorem add_neg_cancel_right (a b: R): (a+b) + -b=a:=
by rw [add_assoc,add_right_neg,add_zero]

theorem add_left_cancel {a b c:R} (h: a+b=a+c): b=c :=
by rw  [←zero_add b, ←add_left_neg a, add_assoc, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
by rw [←add_neg_cancel_right a b, h, add_neg_cancel_right]

end my_ring

namespace my_ring

variables {R:Type*} [ring R]

theorem zero_mul (a:R): 0*a=0 :=
have h:
0*a + 0*a = 0 + 0*a,
begin
rw ←add_mul,
rw add_zero,
rw zero_add
end,
by rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b :R} (h: a+b=0) : -a=b :=
  have h1:
  -a =-a + (a+b),
  by rw [h,add_zero],
by rw [h1,neg_add_cancel_left]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
  have h1: b+a=0,
  by rw [add_comm,h],
by rw [neg_eq_of_add_eq_zero h1]

theorem neg_neg (a : R) : -(-a) = a :=
  have h0:
  -a + a = 0,
  by rw [neg_add_self],

by rw [neg_eq_of_add_eq_zero h0]

end my_ring

namespace my_ring

variables {R : Type*} [ring R]

theorem self_sub (a : R) : a - a = 0 :=
by rw [sub_eq_add_neg, add_neg_eq_zero]

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
by rw [←one_add_one_eq_two, add_mul,one_mul]

end my_ring


