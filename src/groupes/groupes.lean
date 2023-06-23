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

lemma foo (G : Type) [semigroup G] {e : G} (He : ∀ g, g * e = g) {g g' g'' : G} 
  (h1 : g * g' = e) (h2 : g' * g'' = e) : g' * g = e :=
begin
  have : g' * g * g' = g',
  { rw [mul_assoc, h1, He g'] },
  have H : g' * g * g' * g'' = g' * g'',
  { rw [this] },
  rw [h2, mul_assoc, h2, He] at H,
  exact H
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
  swap,
  { intro g,
    obtain ⟨g', hg'⟩ := inv g,
    use g',
    split,
    exact hg',
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg'' },
  { intro g,
    split,
    exact en g,
    obtain ⟨g', hg'⟩ := inv g,
    rw [← hg', mul_assoc],
    suffices : g' * g = e,
    { rw [this, en] },
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg'' }
end