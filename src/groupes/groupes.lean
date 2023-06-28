import deprecated.subgroup
import data.complex.basic
import algebra.group.units

variables (G : Type) [group G]


lemma is_unique_1 (G : Type) [group G] (e1 e2 : G)
  (H1 : ∀ g : G, g*e1=g ∧ e1*g=g ) (H2 : ∀ g : G, g*e2=g ∧ e2*g=g ) : e1=e2 :=
begin
  rw [<- (H1 e2).2, (H2 e1).1],
end 


lemma is_unique_sym_left (G : Type) [group G] (g g' : G) (h : g' * g = 1) : g'= g⁻¹:=
begin 
  rw [<- mul_one g',<-mul_right_inv g,<- mul_assoc,h,one_mul],
end


lemma is_unique_sym_right (G : Type) [group G] (g g' : G) (h : g * g' = 1) : g'= g⁻¹:=
begin 
  rw [<- one_mul g', <- mul_left_inv g, mul_assoc,h,mul_one],
end 


lemma foo1 (G : Type) [group G] (x y : G)
(Hx : x * y = 1 ∧ y * x = 1) : y⁻¹ = x := 
begin 
  rw [<- one_mul y⁻¹, <-Hx.1,mul_assoc,mul_right_inv,mul_one],
end
 

lemma foo2 (G : Type) [group G] (x : G) : (x⁻¹)⁻¹ = x :=
begin 
   exact foo1 G x x⁻¹ (by refine ⟨by exact mul_right_inv x, by exact mul_left_inv x⟩),
end




--lemma subgroup_inter (G H H': Type) [group G]


/-- Pour prouver `is_subgroup` on peut utiliser `split`. Le premier objectif, `is_monoid`,
peut être décomposé plus avec un autre `split`. -/
example (n : ℕ) (hn : 2 ≤ n) : is_subgroup ({z | z ^ n = 1} : set ℂˣ) :=
begin
  split,
    { refine ⟨by rwa [set.mem_set_of_eq, one_pow], λ a b aU bU,_⟩,
      rw set.mem_set_of_eq at *,
      rw [mul_pow, aU, bU,one_mul],},
    { intros a aU,

      rw set.mem_set_of_eq at *,
      rw [inv_pow,aU],
      refl,}
end


lemma foo (G : Type) [semigroup G] {e : G} (He : ∀ g, g * e = g) {g g' g'' : G} 
  (h1 : g * g' = e) (h2 : g' * g'' = e) : g' * g = e :=
begin
  have : g' * g * g' = g':= by rw [mul_assoc, h1, He g'],
  have H : g' * g * g' * g'' = g' * g'' := by rw [this],
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
    refine ⟨ by exact hg',_⟩,
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg''},
  { intro g,
    refine ⟨ by exact g,_⟩,
    obtain ⟨g', hg'⟩ := inv g,
    rw [← hg', mul_assoc],
    suffices : g' * g = e,
    { rw [this, en] },
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg''}
end


example (G : Type) [group G] (H : set G) (h : ∀ g₁ g₂, g₁ ∈ H → g₂ ∈ H → g₁ * g₂ ∈ H )
  (finite : H.finite) : is_subgroup H :=
begin
  sorry,
end