import data.real.basic

--No argument
example ( a b c : ℝ ): (c*b)*a=b*(a*c) :=
begin
rw mul_assoc,
rw mul_comm,
rw mul_assoc
end

--Partial info, one argument
example (a b c :ℝ): a*b*c=b*(a*c):=
begin
rw mul_assoc a,
rw mul_comm a,
rw mul_assoc b,
rw mul_comm a,
end

-- local context 1
example (a b c d e f:ℝ) (h:b*c=e*f):
a*b*c*d=a*e*f*d:=
begin
rw mul_assoc,
rw mul_assoc,
rw ←mul_assoc b,
rw h,
rw ←mul_assoc,
rw ←mul_assoc, 
end

-- local context 2
example (a b c d:ℝ)(hyp:c=b*a-d)(hyp':d=a*b):c=0:=
begin
rw hyp,
rw hyp',
rw mul_comm b a,
rw sub_self
end

section
  
  variables a b c d:ℝ

  example: (a+b)*(c+d)=a*c+a*d+b*c+b*d:=
  calc
  (a+b)*(c+d)=a*(c+d)+b*(c+d): by rw [add_mul]
  ...= a*c+a*d+b*c+b*d: by rw [mul_add, mul_add,←add_assoc]

  example: (a+b)*(a-b)= a^2-b^2 :=
  calc
  (a+b)*(a-b)
  = a * a - (a * b - b * a) - b * b:
  by rw [add_mul, mul_sub, mul_sub,add_sub,sub_add]
  ...
  = a^2-b^2:
  by rw [mul_comm b a, sub_self, sub_sub, zero_add, ←pow_two, ←pow_two]

 end

