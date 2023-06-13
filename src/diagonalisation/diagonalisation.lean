import linear_algebra.charpoly.basic
import linear_algebra.eigenspace.basic


universes u v w

namespace module
namespace End


variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : End R M)


theorem is_eigenvector_implies_is_root{μ : R} (h : f.has_eigenvalue μ) :
  (f.charpoly).is_root μ :=
begin
  sorry,
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
