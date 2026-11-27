module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Opposite shifts in the source of bounded constructible internal Hom -/

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.ProEtale ProEtale.CondensedRing
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj

universe u

namespace WeilII

set_option backward.isDefEq.respectTransparency false in
/-- In the ambient derived category of modules over a commutative condensed ring, derived
internal Hom into a fixed complex commutes with the triangulated shift on the opposite category. -/
public theorem nonempty_condensedDerivedHomCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : Nonempty (((derivedHom Λ X).flip.obj W).CommShift ℤ) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology Ab.{u + 1} X
  have : Abelian.HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    ProEtale.hasFunctorialFlatResolution_sheaf Ab.{u + 1} X
  have : IsGrothendieckAbelian.{u + 1} C := Mod.isGrothendieckAbelian.{u + 1, u + 1, u + 2} _
  let : MonoidalClosed (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    ProEtale.sheafMonoidalClosed Ab.{u + 1} X
  have := isCommMonObj_condensedRingObj Λ X
  have : Abelian.HasFunctorialFlatResolution C :=
    Mod.hasFunctorialFlatResolution (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (R := condensedRingObj Λ X)
  obtain ⟨s, _⟩ := DerivedCategory.nativeInternalHom_contravariant_exact.{u + 2, u + 1} C W
  exact ⟨s⟩

/-- For fixed bounded constructible target, shifting the source of derived internal Hom
by an integer shifts the result by its negative, naturally in the source. -/
public theorem nonempty_boundedConstructibleHomSourceShiftIso
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (W : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (n : ℤ) :
    let D := (boundedConstructibleHom ℓ X).flip.obj W
    Nonempty ((shiftFunctor _ n).op ⋙ D ≅ D ⋙ shiftFunctor _ (-n)) := by
  intro D
  let bc := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
  let ι := bc.ι
  let T := (derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).flip.obj W.obj
  obtain ⟨s⟩ := nonempty_condensedDerivedHomCommShift (Profinite.padicAlgClRingObj ℓ) X.left W.obj
  let : T.CommShift ℤ := s
  let e : D ⋙ ι ≅ ι.op ⋙ T := Iso.refl _
  let : D.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  exact ⟨Functor.isoWhiskerRight (Pretriangulated.shiftFunctorOpIso _ (-n) n
    (neg_add_cancel n)).symm D ≪≫ D.commShiftIso (-n)⟩

end WeilII
