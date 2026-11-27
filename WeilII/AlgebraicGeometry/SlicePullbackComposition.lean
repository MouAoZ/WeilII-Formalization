module

public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
import WeilII.AlgebraicGeometry.CompactificationComponentTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-! # Comparing pullback composition in the slice with composition along scheme maps -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- On two slice maps the two composition constraints agree. Both restrict the ambient
left-derived pullback composition, so faithfulness identifies their components. -/
public theorem upperStarOfMapComp_slice {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (f : X ⟶ Y) (g : Y ⟶ S) :
    boundedConstructibleUpperStarOfMapComp ℓ (X := S) (Y := Y) (W := X) g.left f.left =
      boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext (P := boundedConstructible _)
  exact (boundedConstructibleUpperStarOfMapComp_hom_app_hom ℓ g.left f.left K).trans
    (boundedConstructibleUpperStarComp_hom_app_hom _ ℓ f g K).symm

private theorem compare_compositions {A C : Type*} [Category* A] [Category* C]
    {T₁ T₂ T₃ T₄ : A ⥤ C} (u u' : T₁ ≅ T₂) (v v' : T₃ ≅ T₄)
    (w : T₁ = T₃) (K : A) (hu : u = u') (hv : v = v') :
    (u.symm ≪≫ eqToIso w ≪≫ v).hom.app K =
      u'.inv.app K ≫ eqToHom (congrArg (fun t : A ⥤ C ↦ t.obj K) w) ≫ v'.hom.app K := by
  subst u' v' T₃
  simp

/-- The underlying-scheme square on slice arrows is the inverse composition constraint,
transport along commutativity, and the forward composition constraint in the slice. -/
public theorem upperStarOfMapSquare_slice_app {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    {x : U' ⟶ U} {y : V' ⟶ V} {h : U ⟶ V} {h' : U' ⟶ V'} (w : CommSq x h' h y)
    (K : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMapSquareIso ℓ h h'
      (Over.left_comp_left_eq_of_comp_eq w.w)).hom.app K =
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.app K ≫
        eqToHom (congrArg (fun t ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ t).obj K) w.w) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ h' y).hom.app K := by
  let wF := congrArg (fun t ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ t) w.w
  have step := compare_compositions _ _ _ _ wF K (upperStarOfMapComp_slice ℓ x h)
    (upperStarOfMapComp_slice ℓ h' y)
  dsimp only [boundedConstructibleUpperStarOfMapSquareIso, wF] at *
  transport_compactification_component step

end WeilII
