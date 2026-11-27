module

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Recovering the native Frobenius map in single-complex coordinates -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Endofunctor MonoidalCategory AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The single chart for Frobenius pullback of a native module. It uses the identification
with inverse pushforward on singles and the comparison of the two coefficient models. -/
def nativeSinglePullIso (A : AdicSheaf ℓ (X ↘ Spec (.of k)).geometricFiber) :
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    H.obj (S.obj (E.obj A)) ≅ S.obj (E.obj ((WeilSheaf.frobeniusPullback k ℓ X).obj A)) :=
  (singleLowerStarIso (k := k) (ℓ := ℓ) (X := X)).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X).app A)

/-- In the native pullback chart, the derived action of a Weil sheaf is its original
structure map placed in degree zero. -/
theorem singleFrobenius_eq_native (W : ProEtaleWeilSheaf k ℓ X) :
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    singleFrobenius W = (nativeSinglePullIso (k := k) (X := X) W.carrier).hom ≫
      S.map (E.map W.str.hom) := by
  intro E S
  let c := (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X).hom.app W.carrier
  let a := (singleLowerStarIso (k := k) (ℓ := ℓ) (X := X)).hom.app (E.obj W.carrier)
  change a ≫ S.map (c ≫ E.map W.str.hom) = (a ≫ S.map c) ≫ S.map (E.map W.str.hom)
  rw [S.map_comp, Category.assoc]

/-- A source action in a fully faithful chart, expressed as a map from the original
coefficient pullback to the original coefficient object. -/
def nativeChartMap {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D) [J.Full]
    (H : D ⥤ D) {V : D} {A R : C} (a : V ≅ J.obj A) (b : H.obj (J.obj A) ≅ J.obj R)
    (g : H.obj V ⟶ V) : R ⟶ A :=
  J.preimage (b.inv ≫ H.map a.inv ≫ g ≫ a.hom)

/-- The coefficient map is the prescribed action if and only if the chart is equivariant. -/
theorem nativeChartMap_eq_iff {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    [J.Full] [J.Faithful] (H : D ⥤ D) {V : D} {A R : C} (a : V ≅ J.obj A)
    (b : H.obj (J.obj A) ≅ J.obj R) (g : H.obj V ⟶ V) (s : R ⟶ A) :
    nativeChartMap J H a b g = s ↔ H.map a.hom ≫ b.hom ≫ J.map s = g ≫ a.hom := by
  change J.preimage _ = s ↔ _
  rw [← J.map_injective.eq_iff, J.map_preimage]
  constructor
  · intro h
    have h' := congrArg ((H.map a.hom ≫ b.hom) ≫ ·) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, ← H.map_comp_assoc, a.hom_inv_id,
      H.map_id, Category.id_comp] using h'.symm
  · intro h
    rw [← h, ← H.map_comp_assoc, a.inv_hom_id, H.map_id, Category.id_comp, b.inv_hom_id_assoc]

/-- The native map in the Frobenius chart is the tensor action as soon as it has the
prescribed value on the two pulled-back factors. This is the native quotient square
of `ProEtaleWeilSheaf.tensorπ_str`. -/
theorem tensorStructure_of_generators (F G : ProEtaleWeilSheaf k ℓ X) :
    let T := ProEtaleWeilSheaf.tensor k ℓ X G F
    let R := ProEtale.lowerStar (WeilCoefficients.{u} ℓ)
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
    ∀ (f : (WeilSheaf.frobeniusPullback k ℓ X).obj T.carrier ⟶ T.carrier),
      Functor.LaxMonoidal.μ R F.carrier.X G.carrier.X ≫
          R.map (Mod.tensorπ F.carrier G.carrier) ≫ f.hom =
        (F.str.hom.hom ⊗ₘ G.str.hom.hom) ≫ Mod.tensorπ F.carrier G.carrier →
      f = T.str.hom := by
  intro T R f h
  exact ProEtaleWeilSheaf.frobeniusPullback_tensor_hom_ext (P := F) (M := G)
    (h.trans (ProEtaleWeilSheaf.tensorπ_str F G))

/-- The action in a relative-tensor chart sends a pulled-back pure tensor to the
tensor of the native Weil images of its two factors. -/
@[irreducible] def ActsOnTensorGenerators (F G : ProEtaleWeilSheaf k ℓ X) :
    let T := ProEtaleWeilSheaf.tensor k ℓ X G F
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    ∀ {V}, (V ≅ S.obj (E.obj T.carrier)) → (H.obj V ⟶ V) → Prop :=
  fun {_V} a g ↦
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    let R := ProEtale.lowerStar (WeilCoefficients.{u} ℓ)
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
    let T := ProEtaleWeilSheaf.tensor k ℓ X G F
    let b := nativeSinglePullIso (k := k) (X := X) T.carrier
    let f := nativeChartMap (E ⋙ S) H a b g
    Functor.LaxMonoidal.μ R F.carrier.X G.carrier.X ≫
        R.map (Mod.tensorπ F.carrier G.carrier) ≫ f.hom =
      (F.str.hom.hom ⊗ₘ G.str.hom.hom) ≫ Mod.tensorπ F.carrier G.carrier

/-- The Frobenius equation for a relative-tensor single chart follows from the values
of its recovered native map on pairs of sections. Both factors may be arbitrary. -/
theorem tensorSingleChart_of_generators (F G : ProEtaleWeilSheaf k ℓ X) :
    let T := ProEtaleWeilSheaf.tensor k ℓ X G F
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    ∀ {V} (a : V ≅ S.obj (E.obj T.carrier)) (g : H.obj V ⟶ V),
      ActsOnTensorGenerators F G a g → H.map a.hom ≫ singleFrobenius T = g ≫ a.hom := by
  intro T E S H V a g h
  let b := nativeSinglePullIso (k := k) (X := X) T.carrier
  let f := nativeChartMap (E ⋙ S) H a b g
  unfold ActsOnTensorGenerators at h
  have hf := tensorStructure_of_generators F G f h
  have he := (nativeChartMap_eq_iff (E ⋙ S) H a b g T.str.hom).1 hf
  exact (congrArg (H.map a.hom ≫ ·) (singleFrobenius_eq_native T)).trans he

end WeilII.ExternalProduct
