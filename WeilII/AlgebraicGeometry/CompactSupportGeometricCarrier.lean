module

public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence
import WeilConjectures.WeilSheaf.CondensedModelBaseChange
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.LowerShriekForget
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersionSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

attribute [-instance] AlgebraicGeometry.specOverSpec in
/-- The coefficient vector space of compactly supported Weil cohomology can be computed
on a chosen geometric fiber, as used in Zhang, §2, pp. 2–4. Forget Frobenius in a
compactification over the finite field. Transport the resulting open immersion to the
chosen fiber and the proper map to its base point. Global sections after the proper
pushforward are global sections on the same compactification. On bounded constructible
objects independence of compactification in the condensed coefficient model identifies this
calculation with the chosen geometric compactification. Global sections on the geometric
point are exact, so taking cohomology gives the claimed equivalence. -/
public theorem compactSupport_linearEquiv_geometricFiber
    {k₀ k : Type u} [Field k₀] [Finite k₀] [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)] [Fact (ringChar k ≠ ℓ)]
    {X B : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (b : B ⟶ Spec (.of (AlgebraicClosure k₀))) [IsSeparated b] [LocallyOfFiniteType b]
    [QuasiCompact b] (v : B ≅ (X ↘ Spec (.of k)).geometricFiber)
    (t : Spec (.of (AlgebraicClosure k₀)) ≅ Spec (.of (AlgebraicClosure k)))
    (hv : v.hom ≫ (X ↘ Spec (.of k)).geometricFiberToAlgebraicClosure = b ≫ t.hom)
    (D : WeilComplex k ℓ X) (r : ℤ) :
    Nonempty ((D.compactlySupportedCohomology r).carrier ≃ₗ[PadicAlgCl ℓ]
      (WeilCoefficients.toModuleCat ℓ).obj ((ProEtale.algClosedCompactlySupportedCohomology ℓ b r).obj
        ((ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory.obj (WeilComplex.forget.obj D)))) := by
  let S := Spec (.of k)
  let T := Spec (.of (AlgebraicClosure k₀))
  let a := X ↘ Spec (.of k)
  let s := Spec (.of k) ↘ Spec (.of k)
  have : a.IsOver S := ⟨Category.comp_id a⟩
  have : IsIso s.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 S) (Scheme.specAlgebraicClosure k).hom))
  let c := WeilComplex.lowerShriekCompactification k a
  have ha : a ≫ s = a := Category.comp_id a
  let fbar := Scheme.Hom.geometricFiberMap a ha
  let cg : Compactification fbar := c.geometricFiber ha
  let point := asIso s.geometricFiberToAlgebraicClosure
  let u := t ≪≫ point.symm
  have wf : fbar ≫ point.hom = a.geometricFiberToAlgebraicClosure :=
    Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure a ha
  have w : v.hom ≫ fbar = b ≫ u.hom := by
    apply (cancel_mono point.hom).mp
    simp only [Category.assoc, wf, u, Iso.trans_hom, Iso.symm_hom,
      point.inv_hom_id, Category.comp_id]
    exact hv
  let c' : Compactification b :=
    { Z := cg.Z, g := cg.g ≫ u.inv, i := v.hom ≫ cg.i
      comm := by
        calc
          b = (b ≫ u.hom) ≫ u.inv := by simp
          _ = (v.hom ≫ fbar) ≫ u.inv := congrArg (· ≫ u.inv) w.symm
          _ = (v.hom ≫ cg.i ≫ cg.g) ≫ u.inv := congrArg (fun z ↦ (v.hom ≫ z) ≫ u.inv) cg.comm
          _ = _ := by simp only [Category.assoc]
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let L := WeilComplex.forget.obj D
  let N := (ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory.obj L
  let c₀ := HasCompactification.compactification b
  let out (d : Compactification b) :=
    (ProEtale.adicLowerStar ℓ d.g).rightDerivedFunctor.obj
      ((ProEtale.adicOpenImmersionLowerShriek ℓ d.i).mapDerivedCategory.obj N)
  have compare : Nonempty (out c' ≅ out c₀) := by
    let A := AlgebraicClosure k₀
    have : Fact (ringChar A ≠ ℓ) := ⟨Algebra.ringChar_eq k₀ A ▸ Fact.out⟩
    have : Fact (ringChar A).Prime := ⟨Algebra.ringChar_eq k₀ A ▸ CharP.prime_ringChar k₀⟩
    let B' : Over (Spec (.of A)) := Over.mk b
    let T' : Over (Spec (.of A)) := Over.mk (𝟙 _)
    let f : B' ⟶ T' := Over.homMk b (Category.comp_id b)
    have : LocallyOfFiniteType B'.hom := ‹LocallyOfFiniteType b›
    have : IsSeparated B'.hom := ‹IsSeparated b›
    have : QuasiCompact B'.hom := ‹QuasiCompact b›
    have : LocallyOfFiniteType T'.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 T))
    have : IsSeparated T'.hom := inferInstanceAs (IsSeparated (𝟙 T))
    have : QuasiCompact T'.hom := inferInstanceAs (QuasiCompact (𝟙 T))
    let (Z : Scheme.{u}) : MonObj (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) :=
      Functor.monObjObj (F := ProEtale.upperStarFromPoint Z) _
    let H := (ProEtale.adicSheafDerivedEquivCondensedMod ℓ B).functor.obj N
    have hL := (WeilComplex.objectProperty_iff D.obj).mp D.property
    have hN := ProEtale.DerivedCategory.boundedConstructibleAdic.mapDerivedCategory_adicUpperStar
      v.hom hL
    have hH := (ProEtale.boundedConstructibleAdic_iff_boundedConstructible ℓ k₀ A B' N).mp hN
    let Hc := (⟨H, hH⟩ : (ProEtale.boundedConstructible _).FullSubcategory)
    let e := ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
      ℓ (f := f) c' c₀
    let ec (d : Compactification b) :=
      (ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        ℓ (f := f) d).app Hc
    let em (d : Compactification b) :=
      (ProEtale.adicRightDerivedLowerShriekOfCompactificationCompIso ℓ T d).app N
    exact ⟨(ProEtale.adicSheafDerivedEquivCondensedMod ℓ T).fullyFaithfulFunctor.preimageIso
      (em c' ≪≫ (ec c').symm ≪≫ (ProEtale.boundedConstructible _).ι.mapIso (e.app Hc) ≪≫
        ec c₀ ≪≫ (em c₀).symm)⟩
  obtain ⟨ec⟩ := compare
  let sq : v.symm.hom ≫ c'.i = cg.i ≫ (Iso.refl cg.Z).hom := by
    change v.inv ≫ v.hom ≫ cg.i = cg.i ≫ 𝟙 _
    simp
  let E := ProEtale.adicOpenImmersionLowerShriek ℓ cg.i
  let E' := ProEtale.adicOpenImmersionLowerShriek ℓ c'.i
  let P := ProEtale.adicUpperStar ℓ v.hom
  let openIso : P ⋙ E' ≅ E :=
    Functor.isoWhiskerRight (ProEtale.adicUpperStarIsoLowerStarInv ℓ v) E' ≪≫
      ProEtale.adicOpenImmersionLowerShriekSquareIso ℓ (a := v.symm) (b := Iso.refl cg.Z)
        (j := cg.i) (j' := c'.i) sq ≪≫
      Functor.isoWhiskerLeft E (ProEtale.adicLowerStarId ℓ cg.Z) ≪≫ E.rightUnitor
  let eOpen := ((Functor.mapDerivedCategoryCompIso P E') ≪≫
    Functor.mapDerivedCategoryNatIso openIso).app L
  let sections {Z W : Scheme.{u}} (g : Z ⟶ W) := Functor.rightDerivedFunctorCompIso'
    (ProEtale.adicLowerStar ℓ g) (ProEtale.adicGlobalSections ℓ W)
    (ProEtale.adicLowerStarCompGlobalSectionsIso ℓ g)
  let M := (WeilComplex.derivedLowerShriek k ℓ a).obj D
  let forget := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ S)
  let G := ProEtale.adicGlobalSections ℓ s.geometricFiber
  have : PreservesFiniteColimits G := by dsimp only [G, s]; infer_instance
  let er := (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k ℓ a c).app D.obj
  let H := DerivedCategory.homologyFunctor (WeilCoefficients.{u} ℓ) r
  let eF := (forget.mapDerivedCategoryHomologyFunctorIso r).app M.obj
  let eG := (G.mapDerivedCategoryHomologyFunctorIso r).app (forget.mapDerivedCategory.obj M.obj)
  let eM := G.mapIso eF ≪≫ eG
  let eFor := G.rightDerivedFunctorIsoMapDerivedCategory.symm.app
    (forget.mapDerivedCategory.obj M.obj) ≪≫ G.rightDerivedFunctor.mapIso er
  let eC := (sections cg.g).app (E.mapDerivedCategory.obj L) ≪≫
    (ProEtale.adicGlobalSections ℓ cg.Z).rightDerivedFunctor.mapIso eOpen.symm ≪≫
    (sections c'.g).symm.app (E'.mapDerivedCategory.obj N) ≪≫
    (ProEtale.adicGlobalSections ℓ T).rightDerivedFunctor.mapIso ec
  exact ⟨WeilCoefficients.linearEquivOfIso (eM ≪≫ H.mapIso (eFor ≪≫ eC))⟩

end WeilII
