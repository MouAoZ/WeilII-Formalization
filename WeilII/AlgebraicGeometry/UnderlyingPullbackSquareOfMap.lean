module

public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale

/-! # Underlying component of the bounded pullback square along scheme maps -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- For a commutative square between schemes over possibly different fields, the
bounded-constructible pullback comparison acts on the underlying derived object by the
ambient pullback comparison for the flipped square. -/
public theorem underlyingPullbackSquareOfMap
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    {U Z : Over (Spec (.of k))} {U' Z' : Over (Spec (.of k'))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (j : U ⟶ Z) (j' : U' ⟶ Z') {p : U'.left ⟶ U.left} {q : Z'.left ⟶ Z.left}
    (sq : CommSq p j'.left j.left q)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapSquareIso ℓ j j' sq.w).hom.app M).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq.flip).hom.app M.obj := by
  have comp_heq {D : Type _} [Category.{_} D] {X Y Z X' Y' Z' : D}
      {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X' ⟶ Y'} {v' : Y' ⟶ Z'} (hx : X = X') (hy : Y = Y')
      (hz : Z = Z') (hu : HEq u u') (hv : HEq v v') : HEq (u ≫ v) (u' ≫ v') := by
    subst X' Y' Z'
    cases hu
    cases hv
    rfl
  -- Work with abstract functors so that equality induction affects only the two transports.
  have compare {B C D : Type _} [Category.{_} B] [Category.{_} C] [Category.{_} D]
      {P : ObjectProperty D} {F G R S : B ⥤ P.FullSubcategory} {F' G' R' S' : C ⥤ D}
      (e : F ≅ R) (f : G ≅ S) (e' : F' ≅ R') (f' : G' ≅ S') (w : F = G) (w' : F' = G')
      (θ : R ≅ S) (θ' : R' ≅ S') (hθ : θ = e.symm ≪≫ eqToIso w ≪≫ f)
      (hθ' : θ' = e'.symm ≪≫ eqToIso w' ≪≫ f') (K : B) (K' : C)
      (hx : (R.obj K).obj = R'.obj K') (hy : (F.obj K).obj = F'.obj K')
      (hz : (S.obj K).obj = S'.obj K')
      (he : HEq (e.inv.app K).hom (e'.inv.app K'))
      (hf : HEq (f.hom.app K).hom (f'.hom.app K')) :
      HEq (θ.hom.app K).hom (θ'.hom.app K') := by
    subst θ θ' G G'
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom] using! comp_heq hx hy hz he hf
  let F := fun t : U'.left ⟶ Z.left ↦ boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := U') t
  -- The adjunction supplies the ambient pullback with its derived-category instances.
  let G := fun t : U'.left ⟶ Z.left ↦
    (fun {L : _ ⥤ _} {R : _ ⥤ _} (_ : L ⊣ R) ↦ L)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) t)
  exact eq_of_heq (compare (boundedConstructibleUpperStarOfMapComp ℓ j.left p)
    (boundedConstructibleUpperStarOfMapComp ℓ q j'.left)
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) p j.left)
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j'.left q)
    (congrArg F sq.w) (congrArg G sq.w) (boundedConstructibleUpperStarOfMapSquareIso ℓ j j' sq.w)
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq.flip)
    rfl rfl M M.obj rfl rfl rfl HEq.rfl
    (heq_of_eq (boundedConstructibleUpperStarOfMapComp_hom_app_hom ℓ q j'.left M)))

end WeilII
