module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Scalar reduction of the supported localization boundary -/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- Scalar reduction transports the connecting map of the supported localization triangle.
The closed comparison commutes with the counit. Completing that square to a map of triangles
determines its open component uniquely, since there are no maps from the shifted closed
term to an open direct image. The unit square identifies that component with the open mate. -/
theorem etaleScalarReduction_supportedLocalizationBoundary
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [HasTateTwist A] [HasTateTwist B] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (t : DerivedExtendScalarsTateShiftData A B hρ ha)
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (τ : (derivedExtendScalars hρ ha X).obj L ≅ L') :
    letI := derivedExtendScalarsCommShift hρ ha X
    let Ψ := derivedExtendScalars hρ ha X
    let Φ := reductionSupportedCoefficientChange hρ ha t
    Ψ.map (supportedLocalizationBoundary A i j hij L) ≫
        (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫ (Φ.supportsMap i τ)⟦(1 : ℤ)⟧' =
      (derivedExtendScalarsLowerStarMap hρ ha j).app _ ≫
        (R((j)_*[ModuleCat.{u + 1} B])).map ((derivedExtendScalarsPullbackIso hρ ha j).hom.app L ≫
          (L((j)^*[ModuleCat.{u + 1} B])).map τ.hom) ≫ supportedLocalizationBoundary B i j hij L' := by
  let := derivedExtendScalarsCommShift hρ ha X
  let Ψ := derivedExtendScalars hρ ha X
  let Φ := reductionSupportedCoefficientChange hρ ha t
  let adj := derivedExtendScalarsAdjunction hρ ha X
  let := adj.commShift_of_rightAdjoint ℤ
  let : Ψ.IsTriangulated := adj.isTriangulated_leftAdjoint
  let T := Ψ.mapTriangle.obj
    (supportedLocalizationTriangle A i j L (supportedLocalizationBoundary A i j hij L))
  let T' := supportedLocalizationTriangle B i j L' (supportedLocalizationBoundary B i j hij L')
  have hT : T ∈ distTriang _ := Ψ.map_distinguished _ (supportedLocalizationTriangle_mem_distTriang
    A i j hij L)
  have hT' : T' ∈ distTriang _ := supportedLocalizationTriangle_mem_distTriang B i j hij L'
  let b : T.obj₃ ⟶ T'.obj₃ := (derivedExtendScalarsLowerStarMap hρ ha j).app _ ≫
    (R((j)_*[ModuleCat.{u + 1} B])).map ((derivedExtendScalarsPullbackIso hρ ha j).hom.app L ≫
      (L((j)^*[ModuleCat.{u + 1} B])).map τ.hom)
  have hunit : T.mor₂ ≫ b = τ.hom ≫ T'.mor₂ := by
    change Ψ.map ((derivedUpperStarLowerStarAdjunction _ j).unit.app L) ≫ _ = _
    dsimp only [b, Ψ]
    erw [map_unit_comp_derivedExtendScalarsLowerStarMap_app_assoc hρ ha j L,
      ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
    exact ((derivedUpperStarLowerStarAdjunction _ j).unit.naturality τ.hom).symm
  obtain ⟨c, hc, hδ⟩ := complete_distinguished_triangle_morphism T T' hT hT'
    (Φ.supportsMap i τ) τ.hom (Φ.supportsMap_comp_counit i τ).symm
  let e := (shiftFunctor _ (1 : ℤ)).mapIso
    ((derivedExtendScalarsLowerShriekIso hρ ha i).app ((R(i)^![A]).obj L))
  have : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) := by
    have hs := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar
      (ModuleCat.{u + 1} B) i j (hij ▸ disjoint_compl_left)
      ((derivedExtendScalars hρ ha Z).obj ((R(i)^![A]).obj L))
      ((L((j)^*[ModuleCat.{u + 1} B])).obj L') 1
    exact @Equiv.subsingleton _ _ (Iso.homCongr e (Iso.refl T'.obj₃)) hs
  have hcb : c = b := Triangle.cancel_mor₂_of_subsingleton hT (hc.trans hunit.symm)
  rw [hcb] at hδ
  change (Ψ.map _ ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _) ≫ _ = (_ ≫ _) ≫ _ at hδ
  simp only [Category.assoc] at hδ
  exact hδ

set_option maxRecDepth 4096 in
/-- Moving the cohomological shift inside closed supports commutes with scalar reduction.
Both maps from the shifted closed term lift the same map through the lower-level counit. -/
theorem etaleScalarReduction_shiftSupportedClass
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [HasTateTwist A] [HasTateTwist B] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (t : DerivedExtendScalarsTateShiftData A B hρ ha)
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (τ : (derivedExtendScalars hρ ha X).obj L ≅ L') (n : ℤ)
    (γ : constantComplex A X ⟶ ((R(i)_![ModuleCat.{u + 1} A]).obj ((R(i)^![A]).obj L))⟦n⟧) :
    letI := derivedExtendScalarsCommShift hρ ha X
    let Ψ := derivedExtendScalars hρ ha X
    let Φ := reductionSupportedCoefficientChange hρ ha t
    Φ.mapSupportedClass i ((Ψ.commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso τ)
        (shiftSupportedClass A i n γ) =
      shiftSupportedClass B i n ((Φ.constantComplexIso X).inv ≫ Ψ.map γ ≫
        (Ψ.commShiftIso n).hom.app _ ≫ (Φ.supportsMap i τ)⟦n⟧') := by
  let := derivedExtendScalarsCommShift hρ ha X
  let Ψ := derivedExtendScalars hρ ha X
  let Φ := reductionSupportedCoefficientChange hρ ha t
  have := (rightDerivedUpperShriekAdjunction A i).commShift_of_leftAdjoint ℤ
  have := (rightDerivedUpperShriekAdjunction B i).commShift_of_leftAdjoint ℤ
  let M := (R(i)^![A]).obj L
  let j := i.openComplement.ι
  let J := L((j)^*[ModuleCat.{u + 1} B])
  have hz : IsZero (J.obj (Ψ.obj (((R(i)_![ModuleCat.{u + 1} A]).obj M)⟦n⟧))) := by
    have h := isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
      (ModuleCat.{u + 1} B) i j (i.range_eq_compl_range_openComplement_ι ▸ disjoint_compl_left)
      j (Set.Subset.rfl) ((derivedExtendScalars hρ ha Z).obj M)
    refine ((shiftFunctor _ n).map_isZero h).of_iso ?_
    exact J.mapIso ((Ψ.commShiftIso n).app _ ≪≫ (shiftFunctor _ n).mapIso
      ((derivedExtendScalarsLowerShriekIso hρ ha i).app M)) ≪≫ (J.commShiftIso n).app _
  have key : Ψ.map (((R(i)_![ModuleCat.{u + 1} A]).commShiftIso n).inv.app _ ≫
        (R(i)_![ModuleCat.{u + 1} A]).map (((R(i)^![A]).commShiftIso n).inv.app L)) ≫
      Φ.supportsMap i ((Ψ.commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso τ) =
    (Ψ.commShiftIso n).hom.app _ ≫ (Φ.supportsMap i τ)⟦n⟧' ≫
      ((R(i)_![ModuleCat.{u + 1} B]).commShiftIso n).inv.app _ ≫
      (R(i)_![ModuleCat.{u + 1} B]).map (((R(i)^![B]).commShiftIso n).inv.app L') := by
    refine (existsUnique_comp_counit_of_isZero B i j i.range_eq_compl_range_openComplement_ι hz
      _).unique ?_ rfl
    have h₁ := (rightDerivedUpperShriekAdjunction A i).commShiftIso_inv_app_counit_app ℤ n L
    have h₂ := (rightDerivedUpperShriekAdjunction B i).commShiftIso_inv_app_counit_app ℤ n L'
    simp only [Functor.commShiftIso_comp_inv_app, Category.assoc] at h₁ h₂
    simp only [Category.assoc, Φ.supportsMap_comp_counit, h₂, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    erw [← Ψ.map_comp_assoc]
    rw [Category.assoc, h₁, ← (shiftFunctor _ n).map_comp, Φ.supportsMap_comp_counit,
      (shiftFunctor _ n).map_comp]
    exact Ψ.commShiftIso_hom_naturality_assoc _ _ _
  have hk := congrArg (fun g ↦ (Φ.constantComplexIso X).inv ≫ Ψ.map γ ≫ g) key
  simp only [Functor.map_comp, Category.assoc] at hk
  simp only [SupportedCoefficientChange.mapSupportedClass, shiftSupportedClass, Functor.map_comp,
    Category.assoc]
  exact hk

end WeilII
