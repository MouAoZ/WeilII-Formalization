module

public import WeilII.AlgebraicGeometry.NativePointProjectionCube
public import WeilII.AlgebraicGeometry.NativePointShriekComparison
meta import WeilConjectures.Tactic.ExactByKernel
meta import WeilII.Tactic.SchemeComponentCongruence

/-! # Compact support of a geometric coefficient with specified Weil datum -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option backward.isDefEq.respectTransparency.types false

namespace WeilII.NativePointShriek

universe u

section Projection

variable {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] {U T S : Over (Spec (.of Ω))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

/-- Paste projection equivariance to an equivariant comparison of compactifications,
keeping both in the isomorphism coordinates of the compactified functors. -/
theorem projectionComposite (f : U ⟶ T) (g : U ⟶ S) (y : T ⟶ S)
    (sq : IsPullback (𝟙 U) f g y) [WeaklyEtale y.left]
    (xF : U.left ≅ U.left) (yF : T.left ≅ T.left) (gF : S.left ≅ S.left)
    (hp : CommSq xF.hom f.left f.left yF.hom) (hg : CommSq xF.hom g.left g.left gF.hom)
    (hf : CommSq yF.hom y.left y.left gF.hom) (K : Dᵇc(U.left)⟦Λ⟧)
    (v : (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) xF.hom).obj K ≅ K)
    (t : (CondensedRing.upperStar Λ yF.hom).leftDerivedFunctor ≅
      (CondensedRing.lowerStar Λ yF.inv).mapDerivedCategory) :
    let V := (CondensedRing.lowerStar Λ yF.inv).mapDerivedCategory
    let Ep := purityFieldLowerShriekBaseChange ℓ f f (IsPullback.of_horiz_isIso hp)
    let Eg := purityFieldLowerShriekBaseChange ℓ g g (IsPullback.of_horiz_isIso hg)
    let E := purityFieldLowerShriekBaseChange ℓ g f sq.overLeft
    let i := boundedIdentityPullback ℓ U
    let Hf := boundedConstructibleLowerShriek ℓ f
    let Hg := boundedConstructibleLowerShriek ℓ g
    let Pa := (CondensedRing.upperStar Λ y.left).leftDerivedFunctor
    let I := (boundedConstructible (condensedRingObj Λ T.left)).ι
    let Is := (boundedConstructible (condensedRingObj Λ S.left)).ι
    let pointExchange := Functor.isoWhiskerLeft Pa t.symm ≪≫ (pullbackSquareComparison Λ hf).symm
    let image := Is.mapIso (Eg.app K ≪≫ Hg.mapIso v)
    ∀ {Z : Dᵇc(T.left)⟦Λ⟧} (j : Hf.obj K ≅ Z) {W} (z : I.obj Z ≅ W)
      (dst dst' : V.obj W ⟶ W), dst = dst' →
      IsWeilEquivariant V (t.inv.app _ ≫ (Ep.hom.app K ≫ Hf.map v.hom).hom) dst'
        (I.map j.hom ≫ z.hom) →
      IsWeilEquivariant V (transportWeilDatum Pa pointExchange.symm image.hom) dst
        (I.mapIso (E.app K ≪≫ Hf.mapIso (i.app K) ≪≫ j) ≪≫ z).hom := by
  intro V Ep Eg E i Hf Hg Pa I Is pointExchange image Z j W z dst dst' hdst back
  let src := transportWeilDatum Pa pointExchange.symm image.hom
  let mid := t.inv.app (Hf.obj K).obj ≫ (Ep.hom.app K ≫ Hf.map v.hom).hom
  have front := projectionShriekEquivariance ℓ f g y sq xF yF gF hp hg hf K v.hom t
  refine pasteEquivariantIsoComponents I V (E.app K) (Hf.mapIso (i.app K)) j z
    src mid dst dst' hdst ?_ back
  dsimp only at front
  dsimp only [src, transportWeilDatum, pointExchange, image, Iso.symm_inv, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, ObjectProperty.ι_map, Is, I, mid]
  scheme_component_exact front using hf

end Projection

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]

local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "aX" => X ↘ Spec (CommRingCat.of k)
local notation "Xbar" => Over.mk (Scheme.Hom.geometricFiberToAlgebraicClosure aX)

/-- The algebraic closure has the prime characteristic of the finite base field. -/
private instance nativeCharPrime : Fact (ringChar Ω).Prime :=
  ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩

/-- The residue characteristic stays distinct from the coefficient prime after base change. -/
private instance nativeCharNe : Fact (ringChar Ω ≠ ℓ) :=
  ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

local notation "S₀" => WeilComplex.pointGeometricFiberOver k

/-- For any bounded geometric coefficient with a descent map, the projection followed
by change to the arithmetic compactification intertwines compactly supported descent.
The target action may be specified by its factorization into exchange and input descent. -/
theorem coefficientFrobenius (K : Dᵇc((Xbar).left)⟦Λ⟧)
    (v : (boundedConstructibleUpperStarOfMap ℓ (X := Xbar) (Y := Xbar)
        (aX).geometricGaloisFrobenius.asIso.hom).obj K ≅ K)
    (w : (CondensedRing.lowerStar Λ (aX).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj K.obj ⟶ K.obj)
    (hv : (inversePush (ℓ := ℓ) (aX).geometricGaloisFrobenius.asIso).hom.app K.obj ≫ w = v.hom.hom) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let R := CondensedRing.rightDerivedLowerShriekOfCompactification Λ (WeilComplex.geometricFiberCompactification (k₀ := k) X)
    let V := (CondensedRing.lowerStar Λ (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory
    let P := (CondensedRing.upperStar Λ (S₀).hom).leftDerivedFunctor
    let image :=
      let sq : IsPullback (aX).geometricGaloisFrobenius.asIso.hom
          (toPoint Xbar).left (toPoint Xbar).left (specGeometricFrobenius k).asIso.hom :=
        IsPullback.of_horiz_isIso ⟨by
          rw [toPoint_left]
          exact (aX).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
      (boundedConstructible _).ι.mapIso
        ((purityFieldLowerShriekBaseChange ℓ (toPoint Xbar) (toPoint Xbar) sq).app
          K ≪≫ (boundedConstructibleLowerShriek ℓ (toPoint Xbar)).mapIso
            v)
    let projection :=
      let f := WeilComplex.geometricFiberStructureMorphism (k₀ := k) X
      let c := WeilComplex.geometricFiberCompactification (k₀ := k) X
      let sq : IsPullback (𝟙 (Xbar).left) f.left (toPoint Xbar).left (S₀).hom :=
        IsPullback.of_horiz_isIso ⟨by
          rw [Category.id_comp, toPoint_left]
          exact f.w.symm⟩
      let idK : (boundedConstructibleUpperStarOfMap ℓ (X := Xbar) (Y := Xbar)
          (𝟙 _)).obj K ≅ K := ObjectProperty.isoMk _ ((leftDerivedUpperStarId Λ _).app K.obj)
      (boundedConstructible _).ι.mapIso
          ((purityFieldLowerShriekBaseChange ℓ (toPoint Xbar) f sq).app K ≪≫
            (boundedConstructibleLowerShriek ℓ f).mapIso idK ≪≫
            (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
              (compactificationOverField f) c).app K) ≪≫
        (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).app K
    let pointExchange :=
      let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
      let t := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom ≪≫
        Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ σ)
      let sq : CommSq σ.hom (S₀).hom (S₀).hom (specGeometricFrobenius k).asIso.hom :=
        ⟨(Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
      Functor.isoWhiskerLeft P t.symm ≪≫ (pullbackSquareComparison Λ sq).symm

    ∀ (dst : V.obj (R.obj K.obj) ⟶ R.obj K.obj),
      dst = compactificationInverseFrobeniusComponent Λ C (comp_over aX (Spec (.of k))) K.obj ≫ R.map w →
      IsWeilEquivariant V (transportWeilDatum P pointExchange.symm image.hom) dst projection.hom := by
  intro C R V P image projection pointExchange dst hdst
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let t := inversePush (ℓ := ℓ) σ
  have back := changeCompactification_equivariance K v.hom w hv
  let f := WeilComplex.geometricFiberStructureMorphism (k₀ := k) X
  let c := WeilComplex.geometricFiberCompactification (k₀ := k) X
  let sq : IsPullback (𝟙 (Xbar).left) f.left (toPoint Xbar).left (S₀).hom :=
    .of_horiz_isIso ⟨by rw [Category.id_comp, toPoint_left]; exact f.w.symm⟩
  let j := (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
    (compactificationOverField f) c).app K
  let kC := (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).app K
  let hp := Scheme.Hom.commSq_geometricGaloisFrobenius aX (comp_over aX (Spec (.of k)))
  let y : S₀ ⟶ point Ω := Over.homMk (S₀).hom (Category.comp_id _)
  have : WeaklyEtale y.left := inferInstanceAs (WeaklyEtale (S₀).hom)
  have qs : IsPullback (𝟙 Xbar) f (toPoint Xbar) y :=
    IsPullback.of_map_of_faithful (Over.forget _) sq
  let xF := (aX).geometricGaloisFrobenius.asIso
  let gF := (specGeometricFrobenius k).asIso
  let hg : CommSq xF.hom (toPoint Xbar).left (toPoint Xbar).left gF.hom := ⟨by
    rw [toPoint_left]; exact (aX).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
  let hf : CommSq σ.hom y.left y.left gF.hom :=
    ⟨(Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
  let target := compactificationInverseFrobeniusComponent Λ C (comp_over aX (Spec (.of k))) K.obj ≫ R.map w
  have result := projectionComposite ℓ f (toPoint Xbar) y qs xF σ gF hp hg hf K v t j kC dst target (by exact_by_kernel hdst)
    (by
      dsimp only [changeCompactification, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at back
      scheme_component_exact back using hf)
  simp -implicitDefEqProofs only [boundedIdentityPullback, NatIso.ofComponents.app] at result
  dsimp only [projection, image, pointExchange, P, V]
  scheme_component_exact result using hf

end WeilII.NativePointShriek
