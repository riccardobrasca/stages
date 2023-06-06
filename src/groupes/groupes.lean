import deprecated.subgroup
import data.complex.basic
import algebra.group.units

variables (G : Type) [group G]

/-- Pour prouver `is_subgroup` on peut utiliser `split`. Le premier objectif, `is_monoid`,
peut être décomposé plus avec un autre `split`. -/
example (n : ℕ) (hn : 2 ≤ n) : is_subgroup ({z | z ^ n = 1} : set ℂˣ) :=
begin
  split,
    {
        split,
        {simp},
        {intros a b aU bU,
          simp at *,
          rw [mul_pow, aU, bU],
          norm_num,}
    },
    {intros a aU,
      simp,
      exact aU,
   },
end