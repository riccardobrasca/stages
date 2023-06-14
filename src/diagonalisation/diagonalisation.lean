import linear_algebra.free_module.finite.basic
import linear_algebra.charpoly.basic
import linear_algebra.eigenspace.basic


universes u v w

namespace module
namespace End


variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : End R M)


lemma non_empty_ker_implies_det_zero   (h : f.ker ≠ ⊥) : 
-- I woudl want to have something like this:
-- f.det = 0 :=
-- but i cannot due to the hypothesis on f (End R M)
f.det =0 :=
begin
  sorry,
end


theorem is_eigenvector_implies_is_root{μ : R} (h : f.has_eigenvalue μ) :
  (f.charpoly).is_root μ :=
begin
  rcases (submodule.ne_bot_iff _).1 h with ⟨v, ⟨H, ne0⟩⟩, -- (1)
  rw eigenspace at H, -- (2)
-- Objectif:
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

