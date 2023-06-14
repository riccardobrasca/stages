import linear_algebra.free_module.finite.basic
import linear_algebra.charpoly.basic
import linear_algebra.eigenspace.basic
import linear_algebra.determinant
import linear_algebra.matrix.charpoly.basic

universes u v w

namespace module
namespace End


variables {R : Type u} {V : Type v} [field R]
variables [add_comm_group V] [module R V] [module.finite R V] (f : End R V)

lemma non_empty_ker_implies_det_zero  {g: End R V} (h : g.ker ≠ ⊥) :
  g.det = 0 :=
begin
  by_contra' h0,
  let g2 := linear_map.equiv_of_det_ne_zero g h0, --this is the same as `f`, but Lean knows it is bijective
  apply h,
  rw linear_map.ker_eq_bot,
  intros x y hxy,
  exact g2.injective hxy,
end


theorem is_eigenvector_implies_is_root{μ : R} (h : f.has_eigenvalue μ) :
  (f.charpoly).is_root μ :=
begin
  rcases (submodule.ne_bot_iff _).1 h with ⟨v, ⟨H, ne0⟩⟩, -- (1)
  rw eigenspace at H, -- (2)
  have H1 : (f - (algebra_map R (End R V)) μ).ker ≠ ⊥, -- (3)
  {
    -- This is trivial, I will do it latter. (It's just proving that a set is not empty having an element of the set...)
    sorry,
  },
  have H2 := non_empty_ker_implies_det_zero H1, -- (4)
  rw polynomial.is_root,
  rw ← H2,
  -- I'm stuck here. The goal is literally `det(f - μ • id) = det(f - μ • id)`, but Lean doesn't know that...

-- Objective:
-- (1) v ∈ eigenspace(μ)
-- (2) v ∈ ker(f - μ • id)
-- (3) ker(f - μ • Id) ≠ ∅
-- (4) det(f - μ • Id) = 0
-- (5) f.charpoly(μ) = 0
end

theorem is_root_implies_is_eigenvector{μ : R} (h:  (f.charpoly).is_root μ):
  f.has_eigenvalue μ :=
begin
  sorry,
end

theorem is_root_iff_is_eigenvector{μ : R} :
  (f.charpoly).is_root μ ↔ f.has_eigenvalue μ :=
begin
  split,
  {
    exact is_root_implies_is_eigenvector f,
  },
  {
    exact is_eigenvector_implies_is_root f,
  }
end

