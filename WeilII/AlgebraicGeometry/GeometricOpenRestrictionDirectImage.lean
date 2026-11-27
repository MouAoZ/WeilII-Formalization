module

public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilConjectures.WeilSheaf.Operations
import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- In the open direct image of Zhang, §2, p. 2, forgetting the Weil structure and
identifying the geometric fiber with a chosen model gives the ordinary derived direct
image from the preimage open. The geometric fiber square and the restriction square
give a cartesian square over the identifying isomorphism. Apply open base change to
that square, using exactness of pullback to commute it with placement in degree zero. -/
public theorem geometricPullback_openDirectImage {k : Type u} [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (U : X.Opens) [QuasiCompact U.ι] (G : WeilSheaf k ℓ X)
    {B : Scheme.{u}} (v : B ≅ (X ↘ Spec (.of k)).geometricFiber) (V : B.Opens)
    (hV : V = (v.hom ≫ (X ↘ Spec (.of k)).geometricFiberProj) ⁻¹ᵁ U) :
    Nonempty ((ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory.obj
        (WeilComplex.forget.obj (openImmersionDerivedDirectImageOfRestriction U.ι G)) ≅
      (ProEtale.adicLowerStar ℓ V.ι).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((ProEtale.adicUpperStar ℓ V.ι).obj
          ((ProEtale.adicUpperStar ℓ v.hom).obj G.carrier)))) := by
  subst V
  let a := X ↘ Spec (.of k)
  let b := v.hom ≫ a.geometricFiberProj
  let V := b ⁻¹ᵁ U
  let j := Scheme.Hom.geometricFiberMap U.ι (comp_over U.ι (Spec (.of k)))
  let t := (Scheme.Hom.isPullback_geometricFiberMap U.ι (comp_over U.ι (Spec (.of k)))).flip
  have sq := (isPullback_morphismRestrict b U).of_right' t
  let g := t.lift (b ∣_ U) (V.ι ≫ v.hom) (by rw [morphismRestrict_ι]; exact (Category.assoc ..).symm)
  have sq' : IsPullback V.ι g v.hom j := sq.flip
  have : IsOpenImmersion g := MorphismProperty.of_isPullback sq' inferInstanceAs
    (IsOpenImmersion v.hom)
  obtain ⟨forgetIso⟩ := WeilComplex.nonempty_derivedLowerStar_comp_forget_iso
    (k₀ := k) (l := ℓ) U.ι
  let G₁ := (WeilSheaf.upperStar U.ι).obj G
  let D₁ := WeilSheaf.toComplex.obj G₁
  let e₁ := forgetIso.app D₁
  let e₂ := ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ U)).mapDerivedCategorySingleFunctor 0).app G₁.obj
  let d := ProEtale.adicDerivedBaseChangeIso ℓ sq'
  let comp := (ProEtale.adicUpperStarCompIso ℓ sq'.w.symm).app G.carrier
  let e₃ := ((ProEtale.adicUpperStar ℓ g).mapDerivedCategorySingleFunctor 0).app G₁.carrier
  exact ⟨(ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory.mapIso
    (e₁ ≪≫ (ProEtale.adicLowerStar ℓ j).rightDerivedFunctor.mapIso e₂) ≪≫ d.app _ ≪≫
    (ProEtale.adicLowerStar ℓ V.ι).rightDerivedFunctor.mapIso
      (e₃ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso comp)⟩

end WeilII
