module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Naturality of the derived isomorphism of a square of exact functors -/

open CategoryTheory CategoryTheory.Limits

namespace WeilII

/-- A family of commutation isomorphisms with an exact functor induces commutation
isomorphisms on total right derived functors, respecting compatible pairs of transformations.
On complexes, conjugate the termwise isomorphisms by the invertible derived units. The
defining unit equation for derived transformations gives the square there, and full
faithfulness of precomposition with localization descends both the isomorphisms and the square. -/
public theorem exactRightDerivedSquare
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {T : Type*} (F : T → D ⥤ D) (G : T → C ⥤ C)
    [∀ t, (F t).Additive] [∀ t, (G t).Additive]
    [∀ t, PreservesFiniteLimits (F t)] [∀ t, PreservesFiniteColimits (F t)]
    [∀ t, PreservesFiniteLimits (G t)] [∀ t, PreservesFiniteColimits (G t)]
    (e : ∀ t, J ⋙ F t ≅ G t ⋙ J) :
    ∃ p : ∀ t, J.rightDerivedFunctor ⋙ (F t).rightDerivedFunctor ≅
        (G t).rightDerivedFunctor ⋙ J.rightDerivedFunctor,
      ∀ (a b : T) (f : F a ⟶ F b) (g : G a ⟶ G b)
        (_ : ∀ N, (e a).hom.app N ≫ J.map (g.app N) = f.app (J.obj N) ≫ (e b).hom.app N)
        (M : DerivedCategory C),
        (p a).hom.app M ≫ J.rightDerivedFunctor.map ((Functor.rightDerivedFunctorNatTrans g).app M) =
          (Functor.rightDerivedFunctorNatTrans f).app (J.rightDerivedFunctor.obj M) ≫
            (p b).hom.app M := by
  let c := ComplexShape.up ℤ
  let Q := HomotopyCategory.quotient C c ⋙ DerivedCategory.Qh
  let Q' := HomotopyCategory.quotient D c ⋙ DerivedCategory.Qh
  let W := HomologicalComplex.quasiIso C c
  let : Q.IsLocalization W :=
    Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso C).symm
  let U : J.mapHomologicalComplex c ⋙ Q' ≅ Q ⋙ J.rightDerivedFunctor :=
    Functor.isoWhiskerLeft (HomotopyCategory.quotient C c) (asIso J.rightDerivedFunctorUnit)
  let V (t : T) : (F t).mapHomologicalComplex c ⋙ Q' ≅ Q' ⋙ (F t).rightDerivedFunctor :=
    Functor.isoWhiskerLeft (HomotopyCategory.quotient D c) (asIso (F t).rightDerivedFunctorUnit)
  let S (t : T) : (G t).mapHomologicalComplex c ⋙ Q ≅ Q ⋙ (G t).rightDerivedFunctor :=
    Functor.isoWhiskerLeft (HomotopyCategory.quotient C c) (asIso (G t).rightDerivedFunctorUnit)
  let left (t : T) : (J ⋙ F t).mapHomologicalComplex c ⋙ Q' ≅
      Q ⋙ J.rightDerivedFunctor ⋙ (F t).rightDerivedFunctor :=
    Functor.isoWhiskerLeft (J.mapHomologicalComplex c) (V t) ≪≫
      Functor.isoWhiskerRight U (F t).rightDerivedFunctor
  let right (t : T) : (G t ⋙ J).mapHomologicalComplex c ⋙ Q' ≅
      Q ⋙ (G t).rightDerivedFunctor ⋙ J.rightDerivedFunctor :=
    Functor.isoWhiskerLeft ((G t).mapHomologicalComplex c) U ≪≫
      Functor.isoWhiskerRight (S t) J.rightDerivedFunctor
  let p (t : T) := (Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory D)).preimageIso
    (X := J.rightDerivedFunctor ⋙ (F t).rightDerivedFunctor)
    (Y := (G t).rightDerivedFunctor ⋙ J.rightDerivedFunctor)
    ((left t).symm ≪≫ Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (e t) c) Q' ≪≫ right t)
  refine ⟨p, ?_⟩
  intro a b f g h M
  have fac (t : T) (K : CochainComplex C ℤ) :
      (left t).hom.app K ≫ (p t).hom.app (Q.obj K) =
        Q'.map (((e t).hom.mapHomologicalComplex c).app K) ≫ (right t).hom.app K := by
    have hh := NatTrans.congr_app ((Localization.fullyFaithfulWhiskeringLeft Q W
      (DerivedCategory D)).map_preimage
      ((left t).symm ≪≫ Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (e t) c) Q' ≪≫
        right t).hom) K
    change (p t).hom.app (Q.obj K) = (left t).inv.app K ≫
      Q'.map (((e t).hom.mapHomologicalComplex c).app K) ≫ (right t).hom.app K at hh
    rw [hh, Iso.hom_inv_id_app_assoc]
  have hf (K : CochainComplex D ℤ) : (V a).hom.app K ≫
      (Functor.rightDerivedFunctorNatTrans f).app (Q'.obj K) =
      Q'.map ((f.mapHomologicalComplex c).app K) ≫ (V b).hom.app K :=
    Functor.rightDerivedNatTrans_app (F a).rightDerivedFunctor (F b).rightDerivedFunctor
      (F a).rightDerivedFunctorUnit (F b).rightDerivedFunctorUnit (HomotopyCategory.quasiIso D c)
      (Functor.whiskerRight (f.mapHomotopyCategory c) DerivedCategory.Qh)
      ((HomotopyCategory.quotient D c).obj K)
  have hg (K : CochainComplex C ℤ) : (S a).hom.app K ≫
      (Functor.rightDerivedFunctorNatTrans g).app (Q.obj K) =
      Q.map ((g.mapHomologicalComplex c).app K) ≫ (S b).hom.app K :=
    Functor.rightDerivedNatTrans_app (G a).rightDerivedFunctor (G b).rightDerivedFunctor
      (G a).rightDerivedFunctorUnit (G b).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C c)
      (Functor.whiskerRight (g.mapHomotopyCategory c) DerivedCategory.Qh)
      ((HomotopyCategory.quotient C c).obj K)
  have hl (K : CochainComplex C ℤ) :
      (left a).hom.app K ≫ (Functor.rightDerivedFunctorNatTrans f).app
        (J.rightDerivedFunctor.obj (Q.obj K)) =
      Q'.map ((f.mapHomologicalComplex c).app ((J.mapHomologicalComplex c).obj K)) ≫
        (left b).hom.app K := by
    dsimp only [left, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [Category.assoc]
    erw [(Functor.rightDerivedFunctorNatTrans f).naturality (U.hom.app K)]
    exact (reassoc_of% (hf ((J.mapHomologicalComplex c).obj K))) _
  have hr (K : CochainComplex C ℤ) :
      (right a).hom.app K ≫ J.rightDerivedFunctor.map
        ((Functor.rightDerivedFunctorNatTrans g).app (Q.obj K)) =
      Q'.map ((J.mapHomologicalComplex c).map ((g.mapHomologicalComplex c).app K)) ≫
        (right b).hom.app K := by
    dsimp only [right, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [Category.assoc, ← J.rightDerivedFunctor.map_comp, hg, Functor.map_comp]
    exact (U.hom.naturality_assoc ((g.mapHomologicalComplex c).app K) _).symm
  suffices q : (p a).hom ≫ Functor.whiskerRight (Functor.rightDerivedFunctorNatTrans g) _ =
      Functor.whiskerLeft _ (Functor.rightDerivedFunctorNatTrans f) ≫ (p b).hom from
    NatTrans.congr_app q M
  apply Localization.natTrans_ext Q W
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_epi ((left a).hom.app K), reassoc_of% (fac a K), hr,
    reassoc_of% (hl K), fac]
  rw [← Q'.map_comp_assoc, ← Q'.map_comp_assoc]
  congr 2
  ext n
  exact h (K.X n)

end WeilII
