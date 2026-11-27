module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilII.AlgebraicGeometry.TensorInverseOnefoldMapEvaluation

/-! # Reduction of the evaluation pairing of the ordinary Tate sheaves -/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
  Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

set_option maxHeartbeats 400000

namespace WeilII

/-- Evaluation of the two onefold sheaf powers, pulled back from the exponent base. -/
noncomputable def tateTwistSheafEvaluation (R : Type (u + 1)) [CommRing R] [NeZero (ringChar R)]
    (X : Scheme.{u}) [HasInvertibleExponent R X] :
    tateTwistSheaf R X 1 ⊗ tateTwistSheaf R X (-1) ⟶ 𝟙_ _ :=
  let F := (toInvertibleExponentBase (Λ := R) X)^*[ModuleCat.{u + 1} R]
  μ F _ _ ≫ F.map ((tateSheafTensorInverse R).intTensorFamily.addIso 1 (-1)).hom ≫ η F

private theorem mapTateInverse_left (R : Type (u + 1)) [CommRing R] [NeZero (ringChar R)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : Sheaf (invertibleExponentBase.{u} R).smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ D)
    [F.Monoidal] (hb : ∀ U V, μ F U V ≫ F.map (β_ U V).hom =
      (β_ _ _).hom ≫ μ F V U) :
    ((tateSheafTensorInverse R).map F).leftIso.hom =
      (β_ _ _).hom ≫ ((tateSheafTensorInverse R).map F).rightIso.hom := by
  let e := tateSheafTensorInverse R
  have he : e.leftIso.hom = (β_ _ _).hom ≫ e.rightIso.hom := rfl
  change μ F _ _ ≫ F.map e.leftIso.hom ≫ η F = (β_ _ _).hom ≫
    μ F _ _ ≫ F.map e.rightIso.hom ≫ η F
  rw [he, F.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hb]

private theorem compositePairing {C B D T : Type*} [Category* C] [Category* B] [Category* D]
    [Category* T] [MonoidalCategory C] [MonoidalCategory B] [MonoidalCategory D]
    [MonoidalCategory T] (F : C ⥤ B) (G : D ⥤ T) (E : B ⥤ T) [F.Monoidal] [G.Monoidal]
    [E.Monoidal] {a b : C} {c d : D} (u : a ⊗ b ⟶ 𝟙_ C) (v : c ⊗ d ⟶ 𝟙_ D)
    (p : E.obj (F.obj a) ⟶ G.obj c) (n : E.obj (F.obj b) ⟶ G.obj d)
    (h : μ (F ⋙ E) _ _ ≫ (F ⋙ E).map u ≫ η (F ⋙ E) =
      (p ⊗ₘ n) ≫ μ G _ _ ≫ G.map v ≫ η G) :
    E.map (μ F _ _ ≫ F.map u ≫ η F) ≫ η E =
      δ E _ _ ≫ (p ⊗ₘ n) ≫ μ G _ _ ≫ G.map v ≫ η G := by
  apply (cancel_epi (μ E _ _)).1
  simpa only [comp_μ, comp_η, Functor.comp_map, Functor.map_comp,
    Category.assoc, Functor.Monoidal.μ_δ_assoc] using h

/-- The direct change-of-coefficients isomorphisms for the two onefold Tate sheaves
preserve their evaluation. The comparison holds over the entire scheme. -/
theorem etaleTateSheafEvaluation_reduction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [NeZero (ringChar A)] [NeZero (ringChar B)] (ρ : A →+* B)
    (X : Scheme.{u}) [HasInvertibleExponent A X] [HasInvertibleExponent B X] :
    let E := Sheaf.extendScalars X.smallEtaleTopology ρ
    letI : E.OplaxMonoidal := (Sheaf.monoidal_extendScalars _ ρ).toOplaxMonoidal
    E.map (tateTwistSheafEvaluation A X) ≫ η E =
      δ E _ _ ≫ ((sheafExtendScalarsTateTwistSheafIso ρ X 1).hom ⊗ₘ
        (sheafExtendScalarsTateTwistSheafIso ρ X (-1)).hom) ≫ tateTwistSheafEvaluation B X := by
  let f (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)] [HasInvertibleExponent R X] :=
    (toInvertibleExponentBase (Λ := R) X)^*[ModuleCat.{u+1} R]
  let E := Sheaf.extendScalars X.smallEtaleTopology ρ
  let EM : E.Monoidal := Sheaf.monoidal_extendScalars _ ρ
  let : E.LaxMonoidal := EM.toLaxMonoidal
  let : E.OplaxMonoidal := EM.toOplaxMonoidal
  have b (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)] [HasInvertibleExponent R X]
      (U V : Sheaf (invertibleExponentBase.{u} R).smallEtaleTopology (ModuleCat.{u+1} R)) :
      μ (f R) U V ≫ (f R).map (β_ U V).hom = (β_ _ _).hom ≫ μ (f R) V U :=
    Functor.Monoidal.μ_braiding_of_δ_braiding (fun _ _ ↦
      (upperStar_map_braiding_hom_δ _ _ _ _).symm) U V
  have bE (U V : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)) :
      μ E U V ≫ E.map (β_ U V).hom = (β_ _ _).hom ≫ μ E V U :=
    Functor.Monoidal.μ_braiding_of_δ_braiding (fun _ _ ↦
      (sheafExtendScalars_map_braiding_hom_δ (ρ := ρ) X _ _).symm) U V
  have bF (U V : Sheaf (invertibleExponentBase.{u} A).smallEtaleTopology (ModuleCat.{u+1} A)) :
      μ (f A ⋙ E) U V ≫ (f A ⋙ E).map (β_ U V).hom =
        (β_ _ _).hom ≫ μ (f A ⋙ E) V U := by
    simp only [comp_μ, Functor.comp_map, Category.assoc]
    rw [← E.map_comp, b A, E.map_comp, reassoc_of% bE]
    rfl
  have h := tensorInverse_onefoldMapEvaluation (f A ⋙ E) (f B) (tateSheafTensorInverse A)
    (tateSheafTensorInverse B) (sheafExtendScalarsUpperStarTateSheafIso ρ X)
    ((tateSheafTensorInverse B).map (f B)) (mapTateInverse_left A _ bF)
    (mapTateInverse_left B _ (b B))
  exact compositePairing (f A) (f B) E
    ((tateSheafTensorInverse A).intTensorFamily.addIso 1 (-1)).hom
    ((tateSheafTensorInverse B).intTensorFamily.addIso 1 (-1)).hom
    (sheafExtendScalarsTateTwistSheafIso ρ X 1).hom
    (sheafExtendScalarsTateTwistSheafIso ρ X (-1)).hom h

end WeilII
