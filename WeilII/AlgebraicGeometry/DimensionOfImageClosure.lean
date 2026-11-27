module

public import WeilConjectures.AlgebraicGeometry.ClosurePointDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Topology.KrullDimension.Specialization

/-! # Dimension of the closure of the image of a finite type morphism -/

namespace WeilII

open AlgebraicGeometry CategoryTheory

universe u

/-- The image closure of a finite type map to a scheme locally of finite type over a field
has dimension at most the dimension of its source (the support estimate in Katz A.5, p. 221).
Every point of the closure specializes from an image point by quasi-compactness.
Each such point closure has dimension bounded by its source point closure. -/
public theorem topologicalKrullDim_closure_range_le_source {k : Type u} [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [LocallyOfFiniteType a] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    topologicalKrullDim (closure (Set.range f) : Set Y) ≤ topologicalKrullDim X := by
  apply topologicalKrullDim_le_of_subset_iUnion_closure_singleton (S := Set.range f)
    isClosed_closure
  · intro y hy
    obtain ⟨x, hxy⟩ := exists_specializes_of_mem_closure_range f hy
    exact Set.mem_iUnion₂.mpr ⟨f x, ⟨x, rfl⟩, specializes_iff_mem_closure.mp hxy⟩
  · rintro _ ⟨x, rfl⟩
    exact (Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le a f x).trans
      Topology.IsInducing.subtypeVal.topologicalKrullDim_le

end WeilII
