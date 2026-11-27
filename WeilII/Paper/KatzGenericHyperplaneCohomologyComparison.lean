module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
import WeilII.AlgebraicGeometry.BoundedConstructibleAdicRealization
import WeilII.Paper.KatzGenericHyperplaneExtensionByZeroExchange
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
import WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!
# Cohomology on the complement of a generic hyperplane

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.3–A.4,
pp. 219–220. Taking derived global sections of the hyperplane exchange morphism gives
a comparison from compactly supported cohomology on the hyperplane complement in projective
space to ordinary cohomology on the source of a separated morphism of finite type.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory

universe u

/-- Katz, Corollary A.4, p. 220, for a constructible sheaf in degree zero. With `B = P ∖ H`,
`j : f⁻¹B ↪ X` and `g : f⁻¹B ⟶ B`, the comparison
`H_cʳ(B, Rg_* j^*K) ⟶ Hʳ(X, j_! j^*K)` is natural in constructible `K`. For each `K` it is
invertible for every hyperplane in one dense open of the dual space and for every degree.

Proof. Fix a hyperplane, write `β : B ↪ P` and `p : P ⟶ S`, and put `M = (j^*K)[0]`.
The restriction `g` is a base change of `f`, hence separated of finite type. Pullback
preserves constructibility, so `M` and its derived direct image `A = Rg_* M` are bounded
constructible. Since `p` is proper, `(β,p)` compactifies `B ⟶ S` and computes its exceptional
direct image of `A` as `Rp_* β_! A`. To identify this with the compactification chosen in
compactly supported cohomology, pass both direct images to the condensed coefficient model.
There the image of `A` is bounded constructible and independence of compactification gives
a natural isomorphism by common refinement. Transport it back to the adic model.

Apply `Rp_*` to the adjunction morphism `β_! A ⟶ Rf_* j_! M` of A.3. Exactness of open
extension identifies `j_! M` with `(j_! j^*K)[0]`, and composition of derived direct images
identifies `Rp_* Rf_*` with the derived direct image along the structure morphism of `X`.
Taking derived global sections on the geometric point and degree `r` cohomology gives the
displayed map. These comparisons and the adjunction morphism are natural in `K`. For the
given `K`, A.3 supplies a dense open on which the adjunction morphism is already invertible
before applying global sections. Every cohomology functor therefore gives an isomorphism on
that same open. -/
public theorem exists_denseOpen_isIso_hyperplaneCohomologyComparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (I : Type u) [Fintype I] [Nontrivial I] {X : Scheme.{u}} :
    let k := AlgebraicClosure k₀
    let S := Spec (CommRingCat.of k)
    let P := ℙ(I; S)
    letI : S.Over S := ⟨𝟙 S⟩
    ∀ [X.Over S] (f : X ⟶ P) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f],
      let B := fun (H : S ⟶ P) [H.IsOver S] ↦
        (projectiveHyperplaneFiber H).subschemeι.openComplement
      let j := fun (H : S ⟶ P) [H.IsOver S] ↦ (f ⁻¹ᵁ B H).ι
      let C := ProEtale.adicConstructibleSheaf ℓ X
      let compact := fun (H : S ⟶ P) [H.IsOver S] (r : ℤ) ↦
        let b := (B H).ι ≫ P ↘ S
        letI : HasCompactification b := HasCompactification.comp_of_isOpenImmersion (P ↘ S) (B H).ι
        C.ι ⋙ ProEtale.adicUpperStar ℓ (j H) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          (ProEtale.adicLowerStar ℓ (morphismRestrict f (B H))).rightDerivedFunctor ⋙
          ProEtale.algClosedCompactlySupportedCohomology ℓ b r
      let ordinary := fun (H : S ⟶ P) [H.IsOver S] (r : ℤ) ↦
        C.ι ⋙ ProEtale.adicUpperStar ℓ (j H) ⋙ ProEtale.adicOpenImmersionLowerShriek ℓ (j H) ⋙
          DerivedCategory.singleFunctor _ 0 ⋙ ProEtale.algClosedCohomology ℓ (X ↘ S) r
      ∃ compare : ∀ (H : S ⟶ P) [H.IsOver S] (r : ℤ), compact H r ⟶ ordinary H r,
        ∀ (K : ProEtale.AdicSheaf ℓ X) (hK : ProEtale.IsAdicConstructibleSheaf K),
          ∃ W : P.Opens, Dense (W : Set P) ∧
            ∀ (H : S ⟶ P) [H.IsOver S], H (IsLocalRing.closedPoint k) ∈ W →
              ∀ r : ℤ, IsIso ((compare H r).app ⟨K, hK⟩) := by
  classical
  intro k S P instX f hf hsep hft hqc B j C compact ordinary
  let : S.Over S := ⟨𝟙 S⟩
  have hk : ringChar k ≠ ℓ := Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)
  have : Fact (ringChar k ≠ ℓ) := ⟨hk⟩
  have : Fact (ringChar k).Prime := ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
  let p := P ↘ S
  have : IsNoetherian P := isNoetherian_of_locallyOfFiniteType p
  let input (H : S ⟶ P) [H.IsOver S] :=
    C.ι ⋙ ProEtale.adicUpperStar ℓ (j H) ⋙ DerivedCategory.singleFunctor _ 0
  have comparison (H : S ⟶ P) [H.IsOver S] (r : ℤ) :
      ∃ η : compact H r ⟶ ordinary H r, ∀ K : C.FullSubcategory,
        IsIso ((adicOpenExtensionDirectImageExchange ℓ f (B H)).app ((input H).obj K)) →
          IsIso (η.app K) := by
    let U := B H
    let b := U.ι ≫ p
    let : HasCompactification b := HasCompactification.comp_of_isOpenImmersion p U.ι
    let chosen := HasCompactification.compactification b
    let projective : Compactification b := ⟨P, p, U.ι, rfl, inferInstance, inferInstance⟩
    let T : Over S := Over.mk b
    let point : Over S := Over.mk (𝟙 S)
    let toPoint : T ⟶ point := Over.homMk b (Category.comp_id b)
    have : LocallyOfFiniteType T.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ p))
    have : IsSeparated T.hom := inferInstanceAs (IsSeparated (U.ι ≫ p))
    have : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (U.ι ≫ p))
    have : LocallyOfFiniteType point.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
    have : IsSeparated point.hom := inferInstanceAs (IsSeparated (𝟙 S))
    have : QuasiCompact point.hom := inferInstanceAs (QuasiCompact (𝟙 S))
    let g := morphismRestrict f U
    let A := input H ⋙ (ProEtale.adicLowerStar ℓ g).rightDerivedFunctor
    let E := ProEtale.adicSheafDerivedEquivCondensedMod ℓ U
    let (Y : Scheme.{u}) : MonObj (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) :=
      Functor.monObjObj (F := ProEtale.upperStarFromPoint Y) _
    let Acond := (ProEtale.boundedConstructible _).lift (A ⋙ E.functor) (fun K ↦
      (ProEtale.boundedConstructibleAdic_iff_boundedConstructible ℓ k₀ k T _).1
        (ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj b hk g
          (ProEtale.bounded_homologyProperty_singleFunctor (K.property.upperStar (j H)))))
    let realize : A ≅ Acond ⋙ boundedAdicRealization ℓ U :=
      Functor.isoWhiskerLeft A E.unitIso
    let shriek (d : Compactification b) :=
      (ProEtale.adicOpenImmersionLowerShriek ℓ d.i).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar ℓ d.g).rightDerivedFunctor
    let changeCompactification : A ⋙ shriek chosen ≅ A ⋙ shriek projective :=
      Functor.isoWhiskerRight realize (shriek chosen) ≪≫ Functor.isoWhiskerLeft Acond
        ((boundedShriekAdicRealizationIso ℓ toPoint chosen).symm ≪≫
          boundedShriekAdicRealizationIso ℓ toPoint projective) ≪≫
        Functor.isoWhiskerRight realize.symm (shriek projective)
    let Rp := (ProEtale.adicLowerStar ℓ p).rightDerivedFunctor
    let Rf := (ProEtale.adicLowerStar ℓ f).rightDerivedFunctor
    let D := ProEtale.adicOpenImmersionLowerShriek ℓ (j H)
    let res := C.ι ⋙ ProEtale.adicUpperStar ℓ (j H)
    let cohom := (ProEtale.adicGlobalSections ℓ S).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ r
    let exchange := adicOpenExtensionDirectImageExchange ℓ f U
    let single := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft res (D.mapDerivedCategorySingleFunctor 0)) (Rf ⋙ Rp)
    let comp := Functor.rightDerivedFunctorCompIso' (ProEtale.adicLowerStar ℓ f)
      (ProEtale.adicLowerStar ℓ p) (ProEtale.adicLowerStarComp ℓ f p ≪≫
        ProEtale.adicLowerStarCongr ℓ (comp_over f S))
    let finish := single ≪≫ Functor.isoWhiskerLeft
      (res ⋙ D ⋙ DerivedCategory.singleFunctor _ 0) comp
    refine ⟨Functor.whiskerRight (changeCompactification.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft (input H) exchange) Rp ≫ finish.hom) cohom, ?_⟩
    intro K hK
    change IsIso (cohom.map (changeCompactification.hom.app K ≫
      Rp.map (exchange.app ((input H).obj K)) ≫ finish.hom.app K))
    infer_instance
  refine ⟨fun H _ r ↦ (comparison H r).choose, ?_⟩
  intro K hK
  obtain ⟨W, hW, isoOn⟩ := exists_denseOpen_isIso_hyperplaneExtensionByZeroExchange k₀ ℓ I f K hK
  exact ⟨W, hW, fun H _ hH r ↦ (comparison H r).choose_spec ⟨K, hK⟩ (isoOn H hH)⟩

end WeilII
