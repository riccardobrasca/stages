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
        {
          rw [set.mem_set_of_eq, one_pow],
        },
        {
          intros a b aU bU,
          rw set.mem_set_of_eq at *,
          rw [mul_pow, aU, bU],
          norm_num,
        }
    },
    {
      intros a aU,
      rw set.mem_set_of_eq at *,
      rw [inv_pow,aU],
      refl,
   }
end

/-- `semigroup G` signifie que la multiplication est associative, on peut utiliser
`mul_assoc`. -/
example (G : Type) [semigroup G]
  (H : ∃ (e : G), (∀ g, g * e = g) ∧ (∀ g, ∃ g', g * g' = e)) :
  ∃ (u : G), (∀ g, g * u = g ∧ u * g = g) ∧ (∀ g, ∃ g', g * g' = u ∧ g' * g = u) :=
begin
  sorry
end