module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
meta import WeilConjectures.Tactic.RflByKernel

/-! # Composition on a fixed compactification triangle under change of field structures -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {a : X.left ⟶ Spec (.of k)} {b : Y.left ⟶ Spec (.of k)} {c : Z.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    [LocallyOfFiniteType (Over.mk c).hom] [QuasiCompact (Over.mk c).hom] [IsSeparated (Over.mk c).hom]
    (wf : f.left ≫ b = a) (wg : g.left ≫ c = b)

local notation "f₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf
local notation "g₁" => Over.homMk (U := Over.mk b) (V := Over.mk c) g.left wg
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- The composition isomorphism of a fixed scheme compactification triangle is independent of
the compatible field structures on its vertices. In the formula for `ExchangeFormalism.compIso`
the central exchange is obtained by taking two mates of the pullback square. Both adjunctions
restrict the same ambient adjunctions and the pullback constraints restrict the same ambient
constraints. The open and proper composition isomorphisms are conjugates of those constraints.
Consequently all factors use only the underlying arrows of the triangle. -/
public theorem triangleComposition_changeStructure (T : Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := g) T
    haveI := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := g) T
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (f := f₁) (g := g₁) T
    haveI := isIso_exchange_triangleShriekTriangle ℓ (f := f₁) (g := g₁) T
    (𝔽).compIso (triangleShriekTriangle (f := f₁) (g := g₁) T) =
      (𝔽).compIso (triangleShriekTriangle (f := f) (g := g) T) := by
  rfl_by_kernel

end WeilII
