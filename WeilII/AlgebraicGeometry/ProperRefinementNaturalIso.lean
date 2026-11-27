module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.RefinementCoherence
meta import WeilConjectures.Tactic.RflByKernel

/-! # Proper refinement isomorphisms under a change of field structure -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {a : X.left ⟶ Spec (.of k)} {b : Y.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    (wf : f.left ≫ b = a)

local notation "f₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf

/-- For a proper refinement of compactifications, changing the compatible field structures
preserves its natural transition isomorphism. Use the refinement formula from the pinned
`LowerShriek/ExchangeFormalism.lean` on both sides. Its identity and composition constraints
are adjoint conjugates of pullback constraints. Its exchange is a double mate of the pullback
square. The restricted functors and adjunctions in that expression depend only on the
underlying scheme morphisms, which are the same for the lifted refinement. -/
public theorem properRefinementIso_changeStructure {d v : Compactification f.left}
    (t : Compactification.OverRefinement d v) :
    boundedConstructibleLowerShriekOverRefinementIso ℓ
      (Compactification.overRefinementOfRefinement (f := f₁) t.toRefinement t.isPullback_left) =
        boundedConstructibleLowerShriekOverRefinementIso ℓ t := by
  apply Iso.ext
  unfold boundedConstructibleLowerShriekOverRefinementIso
  rw [boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq]
  rfl_by_kernel

end WeilII
