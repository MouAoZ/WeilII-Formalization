module

public import WeilII.AlgebraicGeometry.EtaleScalarReductionLocalization
public import WeilII.AlgebraicGeometry.EtaleScalarReductionOpenAdjoint
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame

/-! # Transport of a Kummer class through the supported localization boundary -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The boundary on a principal open is compatible with scalar reduction once the open
Kummer class and the positive Tate coefficient isomorphisms are identified.
The shifted open adjunction gives the square on the third term of localization.
Compose it with the connecting-map square and move the double shift inside supports. -/
theorem etaleKummerLocalizationReduction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [HasKummerClass A] [HasKummerClass B] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (t : DerivedExtendScalarsTateShiftData A B hρ ha)
    {U : Scheme.{u}} [HasInvertibleExponent A U] [HasInvertibleExponent B U]
    (f : Γ(U, ⊤)) :
    let V := U.basicOpen f
    let j := V.ι
    letI : HasInvertibleExponent A (V : Scheme) := .of_hom j
    letI : HasInvertibleExponent B (V : Scheme) := .of_hom j
    letI := derivedExtendScalarsCommShift hρ ha U
    letI := derivedExtendScalarsCommShift hρ ha (V : Scheme)
    let Ψ := derivedExtendScalars hρ ha U
    let ΨV := derivedExtendScalars hρ ha (V : Scheme)
    let Φ := reductionSupportedCoefficientChange hρ ha t
    ∀ (p : Ψ.obj (tateObject A U 1) ≅ tateObject B U 1)
      (q : ΨV.obj (tateObject A V 1) ≅ tateObject B V 1),
      NatTrans.CommShift (derivedExtendScalarsPullbackMap hρ ha j) ℤ →
      (Φ.tateShiftIso U 1).hom = (Ψ.commShiftIso (2 : ℤ)).hom.app _ ≫ p.hom⟦(2 : ℤ)⟧' →
      (derivedExtendScalarsPullbackIso hρ ha j).hom.app _ ≫
          (L((j)^*[ModuleCat.{u+1} B])).map p.hom ≫ (leftDerivedUpperStarTateObjectIso j 1).hom =
        ΨV.map (leftDerivedUpperStarTateObjectIso j 1).hom ≫ q.hom →
      ΨV.map (kummerClass A (U.basicOpenUnit f)) ≫
          (ΨV.commShiftIso (1 : ℤ)).hom.app _ ≫ q.hom⟦(1 : ℤ)⟧' =
        (Φ.constantComplexIso V).hom ≫ kummerClass B (U.basicOpenUnit f) →
      Φ.mapSupportedClass _ (Φ.tateShiftIso U 1) (shiftSupportedClass A _ 2 (kummerBoundary A f)) =
        shiftSupportedClass B _ 2 (kummerBoundary B f) := by
  intro V j
  let : HasInvertibleExponent A (V : Scheme) := .of_hom j
  let : HasInvertibleExponent B (V : Scheme) := .of_hom j
  let := derivedExtendScalarsCommShift hρ ha U
  let := derivedExtendScalarsCommShift hρ ha (V : Scheme)
  intro Ψ ΨV Φ p q hs ht hp hκ
  let i := U.zeroLocusSubschemeι {f}
  let RA := R((j)_*[ModuleCat.{u+1} A])
  let RB := R((j)_*[ModuleCat.{u+1} B])
  let JA := L((j)^*[ModuleCat.{u+1} A])
  let JB := L((j)^*[ModuleCat.{u+1} B])
  let oA := leftDerivedUpperStarTateObjectIso (Λ := A) j 1
  let oB := leftDerivedUpperStarTateObjectIso (Λ := B) j 1
  let e := derivedExtendScalarsPullbackIso hρ ha j
  let l := e.hom.app (tateObject A U 1) ≫ JB.map p.hom
  let σ := (Φ.constantComplexIso U).inv
  let α := (leftDerivedUpperStarConstantComplexIso A j).hom ≫ kummerClass A (U.basicOpenUnit f) ≫
    oA.inv⟦(1 : ℤ)⟧'
  let β := (leftDerivedUpperStarConstantComplexIso B j).hom ≫ kummerClass B (U.basicOpenUnit f) ≫
    oB.inv⟦(1 : ℤ)⟧'
  have hinv : ΨV.map oA.inv ≫ l = q.hom ≫ oB.inv := by
    apply (cancel_mono oB.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, l]
    rw [hp, ← ΨV.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hc := derivedExtendScalarsConstantComplexIso_hom_pullback hρ ha j
  have hunit : JB.map σ ≫ e.inv.app (constantComplex A U) ≫
      ΨV.map (leftDerivedUpperStarConstantComplexIso A j).hom ≫ (Φ.constantComplexIso V).hom =
      (leftDerivedUpperStarConstantComplexIso B j).hom := by
    erw [hc, Iso.inv_hom_id_app_assoc, ← JB.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hread : JB.map σ ≫ e.inv.app _ ≫ ΨV.map α ≫
      (ΨV.commShiftIso (1 : ℤ)).hom.app _ ≫ l⟦(1 : ℤ)⟧' = β := by
    simp only [α, β, ΨV.map_comp, Category.assoc]
    rw [ΨV.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, hinv, Functor.map_comp,
      reassoc_of% hκ, reassoc_of% hunit]
  let aA := (derivedUpperStarLowerStarAdjunction _ j).unit.app (constantComplex A U) ≫
    RA.map α ≫ (RA.commShiftIso (1 : ℤ)).hom.app _
  let aB := (derivedUpperStarLowerStarAdjunction _ j).unit.app (constantComplex B U) ≫
    RB.map β ≫ (RB.commShiftIso (1 : ℤ)).hom.app _
  let b := (derivedExtendScalarsLowerStarMap hρ ha j).app _ ≫ RB.map l
  have hopen : σ ≫ Ψ.map aA ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫ b⟦(1 : ℤ)⟧' = aB := by
    have h := etaleScalarReduction_shiftedAdjoint hρ ha j (constantComplex A U) _ _
      (1 : ℤ) α l hs
    change σ ≫ _ = _
    rw [show Ψ.map aA ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫ b⟦(1 : ℤ)⟧' = _ from h]
    erw [← Adjunction.unit_naturality_assoc, ← RB.map_comp_assoc, hread]
  let δA := supportedLocalizationBoundary A i j (range_zeroLocusSubschemeι_singleton f)
    (tateObject A U 1)
  let δB := supportedLocalizationBoundary B i j (range_zeroLocusSubschemeι_singleton f)
    (tateObject B U 1)
  have hδ : Ψ.map δA ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫
      (Φ.supportsMap i p)⟦(1 : ℤ)⟧' = b ≫ δB := by
    have h := etaleScalarReduction_supportedLocalizationBoundary hρ ha t i j
      (range_zeroLocusSubschemeι_singleton f) _ _ p
    simpa only [b, Category.assoc] using! h
  have hb : σ ≫ Ψ.map (kummerBoundary A f) ≫ (Ψ.commShiftIso (2 : ℤ)).hom.app _ ≫
      (Φ.supportsMap i p)⟦(2 : ℤ)⟧' = kummerBoundary B f := by
    rw [kummerBoundary_eq A, kummerBoundary_eq B]
    change σ ≫ Ψ.map (aA ≫ (δA⟦(1 : ℤ)⟧' ≫ _)) ≫ _ = aB ≫ δB⟦(1 : ℤ)⟧' ≫ _
    rw [Ψ.map_comp, Category.assoc, Functor.map_shift_comp_shiftFunctorAdd'_inv, hδ,
      (shiftFunctor _ (1 : ℤ)).map_comp, Category.assoc, reassoc_of% hopen]
  have he : Φ.tateShiftIso U 1 = (Ψ.commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso p := Iso.ext ht
  rw [he]
  exact (etaleScalarReduction_shiftSupportedClass hρ ha t i p 2 (kummerBoundary A f)).trans
    (congrArg (shiftSupportedClass B i 2) hb)

end WeilII
