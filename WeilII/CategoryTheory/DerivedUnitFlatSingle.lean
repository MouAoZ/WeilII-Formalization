module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat
import all Mathlib.Algebra.Homology.Localization

/-! # The derived oplax unit in its flat degree-zero model -/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

namespace WeilII

/-- On the flat unit, the oplax unit of the left derived functor is computed by the
flat single comparison followed by the degree-zero image of the original oplax unit. -/
theorem leftDerivedUnit_flatSingle {C : Type v} {D : Type w}
    [Category.{u+1} C] [Abelian C] [IsGrothendieckAbelian.{u+1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{u+1} D] [Abelian D] [IsGrothendieckAbelian.{u+1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint]
    [F.Monoidal] (hflat : ObjectProperty.flat (𝟙_ C)) :
    let := F.leftDerivedFunctorOplaxMonoidal
    η F.leftDerivedFunctor =
      F.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app (𝟙_ _)) ≫
      (F.leftDerivedFunctorSingleFunctorIsoOfFlat hflat).hom ≫
      (DerivedCategory.singleFunctor D 0).map (η F) ≫
      (DerivedCategory.quotientCompQhIso D).inv.app (𝟙_ _) := by
  change F.leftDerivedFunctor.map _ ≫ F.leftDerivedFunctorCounit.app _ ≫
      _root_.DerivedCategory.Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ _ = _
  rw [Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η]
  simp only [Functor.leftDerivedFunctorSingleFunctorIsoOfFlat, Functor.mapCochainComplexεIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom, Functor.Monoidal.εIso_inv,
    Functor.map_comp, Category.assoc]
  have hεC : ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have hεD : ε (_root_.DerivedCategory.Qh (C := D)) = 𝟙 _ := rfl
  have := _root_.DerivedCategory.isIso_ε_Qh D
  have hinvD : CategoryTheory.inv (ε (_root_.DerivedCategory.Qh (C := D))) = 𝟙 _ :=
    IsIso.inv_eq_of_hom_inv_id ((Category.comp_id _).trans hεD)
  have hi (K) : (_root_.DerivedCategory.quotientCompQhIso C).inv.app K = 𝟙 _ := rfl
  have hj (K) : (_root_.DerivedCategory.quotientCompQhIso D).hom.app K = 𝟙 _ := rfl
  have hF (K) : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  have hQ {K L : CochainComplex D ℤ} (g : K ⟶ L) :
      _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient D _).map g) =
        _root_.DerivedCategory.Q.map g := by
    have h := _root_.DerivedCategory.quotientCompQhIso_hom_naturality g
    rw [hj, hj] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  have hj' (K) : (_root_.DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := rfl
  erw [hεC, hinvD, hi, hj, hF, hj']
  erw [F.leftDerivedFunctor.map_id, _root_.DerivedCategory.Qh.map_id]
  let i := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (𝟙_ C)
  let j := (HomologicalComplex.single D (.up ℤ) 0).map (η F)
  let q := HomotopyCategory.quotient D (.up ℤ)
  have hcomp : _root_.DerivedCategory.Qh.map (q.map i ≫ q.map j) =
      _root_.DerivedCategory.Q.map i ≫ _root_.DerivedCategory.Q.map j :=
    (_root_.DerivedCategory.Qh.map_comp _ _).trans
      (congrArg₂ (fun l r ↦ l ≫ r) (hQ i) (hQ j))
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  exact congrArg (fun r ↦ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫ r) hcomp

end WeilII
