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
 
lemma sym_sym_x (G : Type) [group G] (x : G) : (x⁻¹)⁻¹ = x :=
begin 
   exact foo1 G x x⁻¹ ⟨mul_right_inv x, mul_left_inv x⟩,
end

lemma subgroup_inter (G: Type) [group G] {H H' : set G}
(subH : is_subgroup H) (subH' : is_subgroup H') : is_subgroup (H ∩ H') :=
begin
  split,
  {split,
    { rw [set.mem_inter_iff],
      refine ⟨subH.1.1, subH'.1.1⟩,},
    { intros a b aHH' bHH',
      rw [set.mem_inter_iff],
      refine ⟨subH.1.2 aHH'.1 bHH'.1, subH'.1.2 aHH'.2 bHH'.2⟩,}},
  { intros a aHH',
    rw [set.mem_inter_iff],
    refine ⟨subH.2  aHH'.1, subH'.2 aHH'.2,⟩}
end  

#check set.mem_inter_iff

lemma subgroup_inter_golfe (G: Type) [group G] {H H' : set G}
(subH : is_subgroup H) (subH' : is_subgroup H') : is_subgroup (H ∩ H') :=
begin
  refine ⟨_,λ a aHH',_⟩,
  {refine ⟨_,λ a b aHH' bHH',_⟩,
    { rw [set.mem_inter_iff],
      refine ⟨subH.1.1, subH'.1.1⟩,},
    { rw [set.mem_inter_iff],
      refine ⟨subH.1.2 aHH'.1 bHH'.1, subH'.1.2 aHH'.2 bHH'.2⟩,}}, 
  { rw [set.mem_inter_iff],
    refine ⟨subH.2  aHH'.1, subH'.2 aHH'.2,⟩}
end 

lemma subgroup_inter2 (G: Type) [group G] (n : ℕ) (f : fin n → set G) 
  (hf : ∀ x, is_subgroup (f x)) : is_subgroup (set.Inter f) :=
begin
  refine ⟨_,λ a afi, set.mem_Inter.2 (λ i, (hf i).2 ((set.mem_Inter.1 afi) i))⟩,
   refine ⟨ set.mem_Inter.2 (λ i, (hf i).1.1), λ a b afi bfi, set.mem_Inter.2 (λ i, (hf i).1.2 (( set.mem_Inter.1 afi) i) ((set.mem_Inter.1 bfi) i))⟩,
end 


-- golfed version of the previous lemma
lemma subgroup_interv2 (G: Type) [group G] (n : ℕ) (f : fin n → set G) 
  (hf : ∀ x, is_subgroup (f x)) : is_subgroup (set.Inter f) := 
  ⟨⟨set.mem_Inter.2 (λ i, (hf i).1.1), 
  λ _ _ afi bfi, set.mem_Inter.2 (λ i, (hf i).1.2 ((set.mem_Inter.1 afi) i) ((set.mem_Inter.1 bfi) i))⟩, 
  λ _ afi, set.mem_Inter.2 (λ i, (hf i).2 ((set.mem_Inter.1 afi) i))⟩

example (n : ℕ) (hn : 2 ≤ n) : is_subgroup ({z | z ^ n = 1} : set ℂˣ) :=
begin
  split,
    { refine ⟨by rwa [set.mem_set_of_eq, one_pow], λ a b aU bU,_⟩,
      rw set.mem_set_of_eq at *,
      rw [mul_pow, aU, bU,one_mul]},
    { intros a aU,
      rw set.mem_set_of_eq at *,
      rw [inv_pow,aU,inv_one]}
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
  { intro g,
    refine ⟨ by exact en g,_⟩,
    obtain ⟨g', hg'⟩ := inv g,
    rw [← hg', mul_assoc],
    suffices : g' * g = e,
    { rw [this, en] },
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg''},
  { intro g,
    obtain ⟨g', hg'⟩ := inv g,
    use g',
    refine ⟨ by exact hg',_⟩,
    obtain ⟨g'', hg''⟩ := inv g',
    exact foo G en hg' hg''}
end

example (G : Type) [group G] (H : set G) (h : ∀ g₁ g₂, g₁ ∈ H → g₂ ∈ H → g₁ * g₂ ∈ H )
  (finite : H.finite) : is_subgroup H :=
begin
  split,
  {
    split,
    {
      sorry
    },
    { intros a b aH bH,
      exact h a b aH bH}
  },
  {
    sorry
  }
end