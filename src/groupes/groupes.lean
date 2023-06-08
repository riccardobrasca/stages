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
      refine ⟨by rwa [set.mem_set_of_eq, one_pow], λ a b aU bU,_⟩,
      rw set.mem_set_of_eq at *,
      rw [mul_pow, aU, bU,one_mul],
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
  rcases H with ⟨e,h⟩,
  rcases h with ⟨en,inv⟩,
  use e,
  split,
  {
    intro g,
    specialize en g,
    refine ⟨by exact en,_⟩,
    {
      specialize inv g,
      cases inv with g' inv,
      have g'g : g'*g = e,
      {
        sorry
      },
      rw [<- inv, mul_assoc,g'g,en],
    } 
  },
  {
    intro g,
    specialize inv g,
    cases inv with g' inv,
    have g'g : g'*g = e,
      {
        sorry
      },
    use g',
    refine ⟨by exact inv,by exact g'g⟩,
  }
end