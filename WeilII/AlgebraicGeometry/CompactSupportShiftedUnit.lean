module

public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityShriekWeilUniversality
public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekTrace
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalar
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
import WeilII.AlgebraicGeometry.NativePointCoefficientFrobenius
meta import WeilConjectures.Tactic.ExactByKernel
import WeilII.AlgebraicGeometry.ShiftedUnitScalarTransport
import WeilII.AlgebraicGeometry.ShiftedPullbackUnitSquare
import WeilII.AlgebraicGeometry.SingleUnitWeilDatum
meta import WeilII.AlgebraicGeometry.CompactificationComponentTransport
import WeilII.CategoryTheory.SingleHomologyDescent
import WeilII.CategoryTheory.DescentOnRepresentatives
public import WeilII.AlgebraicGeometry.CompactifiedWeilFrobenius

/-! # Shifted-unit representatives of compactly supported Weil cohomology

Zhang, p. 2, uses Frobenius-equivariant cohomology classes in the Künneth injection.
Here the geometric model is the condensed compact-support functor to the algebraic closure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option maxSynthPendingDepth 10
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace WeilII.CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]

local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "aX" => X ↘ Spec (CommRingCat.of k)
local notation "Xbar" => Over.mk (Scheme.Hom.geometricFiberToAlgebraicClosure aX)

/-- The algebraic closure has the prime characteristic of the finite base field. -/
private instance closureCharPrime : Fact (ringChar Ω).Prime :=
  ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩

/-- The residue characteristic stays distinct from the coefficient prime after base change. -/
private instance closureCharNe : Fact (ringChar Ω ≠ ℓ) :=
  ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

/-- Condensed coefficient modules on the pro-étale site, as in `TraceFormula.PointTrace`. -/
abbrev Coeff (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)

/-- The ambient derived pullback used by compactification exchange. -/
abbrev pull {T S : Scheme.{u}} (f : T ⟶ S) :
    DerivedCategory (Coeff ℓ S) ⥤ DerivedCategory (Coeff ℓ T) :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) f).leftDerivedFunctor

/-- The geometric carrier of a Weil sheaf in degree zero, using the condensed model of
`WeilComplex.boundedConstructible_condensedCarrier`. -/
def carrier : WeilSheaf k ℓ X ⥤ Dᵇc((Xbar).left)⟦Λ⟧ :=
  (boundedConstructible _).lift
    (WeilSheaf.toComplex ⋙ (WeilComplex.objectProperty k ℓ X).ι ⋙
      (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor ⋙
      (IsoAlgebra.forget _).mapDerivedCategory)
    (fun N ↦ WeilComplex.boundedConstructible_condensedCarrier (WeilSheaf.toComplex.obj N))

/-- Apply the geometric compact-support functor to the carrier and include in the ambient
derived category at the point, as in `CondensedRing.boundedConstructibleLowerShriek`. -/
def shriekImage : WeilSheaf k ℓ X ⥤ DerivedCategory (PointMod ℓ Ω) :=
  carrier ⋙ boundedConstructibleLowerShriek ℓ (toPoint Xbar) ⋙ (boundedConstructible _).ι

/-- Pullback carries the shifted tensor unit to the shifted tensor unit using the shift and
monoidal constraints of the derived pullback. -/
def pullUnit {T S : Scheme.{u}} (f : T ⟶ S) (n : ℤ) :
    (pull (ℓ := ℓ) f).obj ((shiftFunctor _ n).obj (𝟙_ (DerivedCategory (Coeff ℓ S)))) ≅
      (shiftFunctor _ n).obj (𝟙_ (DerivedCategory (Coeff ℓ T))) :=
  ((pull (ℓ := ℓ) f).commShiftIso n).app (𝟙_ _) ≪≫
    (shiftFunctor _ n).mapIso (leftDerivedUpperStarUnitIso Λ f)

/-- The Weil structure on the geometric carrier in pullback coordinates, from
`IsoAlgebra.derivedStrIso` and the identification of pullback with inverse pushforward. -/
def carrierFrobenius (N : WeilSheaf k ℓ X) :
    (boundedConstructibleUpperStarOfMap ℓ (X := Xbar) (Y := Xbar)
      (aX).geometricGaloisFrobenius.asIso.hom).obj (carrier.obj N) ≅ carrier.obj N :=
  ObjectProperty.isoMk _
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ _).app _ ≪≫
      (Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoLowerStarInv Λ (aX).geometricGaloisFrobenius.asIso)).app _ ≪≫
      (IsoAlgebra.derivedStrIso _).app
        ((ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj
          (WeilSheaf.toComplex.obj N).obj))

/-- Frobenius on the geometric compact-support image. The compactification base change is
the open and proper exchange with comparison to the Nagata compactification. -/
def imageFrobenius (N : WeilSheaf k ℓ X) :
    (pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom).obj (shriekImage.obj N) ≅
      shriekImage.obj N :=
  let sq : IsPullback (aX).geometricGaloisFrobenius.asIso.hom
      (toPoint Xbar).left (toPoint Xbar).left (specGeometricFrobenius k).asIso.hom :=
    IsPullback.of_horiz_isIso ⟨by
      rw [toPoint_left]
      exact (aX).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
  (boundedConstructible _).ι.mapIso
    ((purityFieldLowerShriekBaseChange ℓ (toPoint Xbar) (toPoint Xbar) sq).app
      (carrier.obj N) ≪≫ (boundedConstructibleLowerShriek ℓ (toPoint Xbar)).mapIso
        (carrierFrobenius N))

local notation "S₀" => WeilComplex.pointGeometricFiberOver k
local notation "B" N =>
  Functor.obj (WeilComplex.derivedLowerShriek k ℓ aX) (Functor.obj WeilSheaf.toComplex N)

/-- At the native geometric point, compare geometric compact support with the actual
base change of the compactification used by the native Weil direct image.
See `purityFieldLowerShriekBaseChange` and `geometricFiberCompactification`. -/
def atNativePoint (N : WeilSheaf k ℓ X) :
    (pull (ℓ := ℓ) (S₀).hom).obj (shriekImage.obj N) ≅
      (rightDerivedLowerShriekOfCompactification Λ
        (WeilComplex.geometricFiberCompactification (k₀ := k) X)).obj (carrier.obj N).obj :=
  let f := WeilComplex.geometricFiberStructureMorphism (k₀ := k) X
  let c := WeilComplex.geometricFiberCompactification (k₀ := k) X
  let K := carrier.obj N
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

/-- The native direct image, first realized in the condensed model and then forgotten, at
the same compactification. See `derivedLowerShriekCompToCondensedIso` and
`weilRightDerivedLowerShriekCompForgetIso`. -/
def nativeComparison (N : WeilSheaf k ℓ X) :
    (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor.obj
        (WeilComplex.forget.obj (B N)) ≅
      (rightDerivedLowerShriekOfCompactification Λ
        (WeilComplex.geometricFiberCompactification (k₀ := k) X)).obj (carrier.obj N).obj :=
  let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
  let h := comp_over aX (Spec (.of k))
  let M := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj
    (WeilSheaf.toComplex.obj N).obj
  (WeilComplex.condensedCarrierIso (B N).obj).symm ≪≫
    (IsoAlgebra.forget _).mapDerivedCategory.mapIso
      ((WeilComplex.derivedLowerShriekCompToCondensedIso k ℓ aX).app (WeilSheaf.toComplex.obj N)) ≪≫
    (weilRightDerivedLowerShriekCompForgetIso Λ C h).app M

/-- Under the adic/condensed equivalence the native regular module in degree `i` is the
shifted derived tensor unit. Its generator is fixed by the regular-module unit comparison. -/
def singleUnit (T : Scheme.{u}) (i : ℤ) :
    (adicSheafDerivedEquivCondensedMod ℓ T).functor.obj
      ((DerivedCategory.singleFunctor _ i).obj (AdicSheaf.unit ℓ T)) ≅
      (shiftFunctor _ (-i)).obj (𝟙_ (DerivedCategory (Coeff ℓ T))) :=
  ((adicSheafEquivCondensedMod ℓ T).functor.mapDerivedCategorySingleFunctor i).app _ ≪≫
    (DerivedCategory.singleFunctor _ i).mapIso (adicSheafEquivCondensedModTensorUnitIso ℓ T) ≪≫
    (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by lia)).app _).symm ≪≫
    (shiftFunctor _ (-i)).mapIso
      ((DerivedCategory.quotientCompQhIso (Coeff ℓ T)).symm.app (𝟙_ (CochainComplex (Coeff ℓ T) ℤ)))

/-- Read a shifted-unit morphism on the native point by taking cohomology and evaluating
at one. The two compactification comparisons above fix the normalization. -/
def evaluate (N : WeilSheaf k ℓ X) (i : ℤ) (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    (N.compactlySupportedCohomology i).carrier :=
  let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
  let U := AdicSheaf.unit ℓ (S₀).left
  let w : (DerivedCategory.singleFunctor _ i).obj U ⟶ WeilComplex.forget.obj (B N) :=
    E.preimage ((singleUnit (ℓ := ℓ) (S₀).left i).hom ≫ (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv ≫
      (pull (ℓ := ℓ) (S₀).hom).map v ≫ (atNativePoint N).hom ≫ (nativeComparison N).inv)
  let forget := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
  globalSectionOfModHom (DerivedCategory.homSingleToHomology U i _ w ≫
    (forget.mapDerivedCategoryHomologyFunctorIso i).inv.app (B N).obj)

/-- A representative transported back to the single native regular module in degree `i`. -/
def nativeRepresentative (N : WeilSheaf k ℓ X) (i : ℤ)
    (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    (DerivedCategory.singleFunctor _ i).obj (AdicSheaf.unit ℓ (S₀).left) ⟶
      WeilComplex.forget.obj (B N) :=
  (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor.preimage
    ((singleUnit (ℓ := ℓ) (S₀).left i).hom ≫ (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv ≫
      (pull (ℓ := ℓ) (S₀).hom).map v ≫ (atNativePoint N).hom ≫ (nativeComparison N).inv)

/-- Evaluation of a representative already in native coordinates. -/
def nativeValue (D : WeilComplex k ℓ (Spec (.of k))) (i : ℤ)
    (w : (DerivedCategory.singleFunctor _ i).obj (AdicSheaf.unit ℓ (S₀).left) ⟶
      WeilComplex.forget.obj D) : (D.cohomologyFrobeniusModule i).carrier :=
  let F := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
  globalSectionOfModHom (DerivedCategory.homSingleToHomology _ i _ w ≫
    (F.mapDerivedCategoryHomologyFunctorIso i).inv.app D.obj)

/-- On the geometric fiber of the base point, evaluation is a bijection in every degree. -/
theorem evaluate_bijective (N : WeilSheaf k ℓ X) (i : ℤ) :
    Function.Bijective (evaluate N i) := by
  let T := (S₀).left
  let p := (S₀).hom
  have : IsIso p := inferInstanceAs (IsIso (S₀).hom)
  let U := AdicSheaf.unit ℓ T
  have hU : Projective (AdicSheaf.unit ℓ (Spec (.of Ω))) :=
    ((adicSheafEquivCondensedMod ℓ _).map_projective_iff _).mp
      (Projective.of_iso (adicSheafEquivCondensedModTensorUnitIso ℓ _).symm
        (projective_tensorUnit_pointMod ℓ Ω))
  have : Projective U := Projective.of_iso (adicUpperStarUnitIso (l := ℓ) p)
    ((adicUpperStar ℓ p).asEquivalence.toAdjunction.map_projective _ hU)
  let P := pull (ℓ := ℓ) p
  have : P.IsEquivalence := inferInstanceAs (CondensedRing.upperStar Λ p).leftDerivedFunctor.IsEquivalence
  let E := (adicSheafDerivedEquivCondensedMod ℓ T).functor
  -- The two equivalences act on morphisms in opposite directions.
  let D := WeilComplex.forget.obj (B N)
  let s := singleUnit (ℓ := ℓ) T i
  let t := pullUnit (ℓ := ℓ) p (-i)
  let b := atNativePoint N ≪≫ (nativeComparison N).symm
  let H := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
    ).mapDerivedCategoryHomologyFunctorIso i
  let e := (Functor.FullyFaithful.ofFullyFaithful P).homEquiv.trans <|
    ((t ≪≫ s.symm).homCongr b).trans <|
    (Functor.FullyFaithful.ofFullyFaithful E).homEquiv.symm.trans <|
    (DerivedCategory.homSingleEquivOfProjective U i D).trans <|
    ((Iso.refl U).homCongr (H.app (B N).obj).symm).trans <|
    Equiv.ofBijective _ (bijective_globalSectionOfModHom _)
  have he (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) : evaluate N i v = e v := by
    change _ = globalSectionOfModHom (𝟙 U ≫
      DerivedCategory.homSingleToHomology U i D
        (E.preimage ((s.hom ≫ t.inv) ≫ P.map v ≫ b.hom)) ≫ H.inv.app _)
    simp only [Category.assoc, b, Iso.trans_hom, Iso.symm_hom]
    rfl
  exact (funext he) ▸ e.bijective

/-- Naturality of the geometric compactification comparison at the native point.
Source: the natural isomorphisms in `SmoothPurityFieldCompactificationExchange` and
`BoundedConstructibleLowerStar`, and the identity-pullback isomorphism.

Write f for the native structure morphism and c for its geometric compactification.
The base-change isomorphism in `atNativePoint` gives a square for the carrier of g.
The components of identity pullback form a natural isomorphism by the naturality of
`leftDerivedUpperStarId` on underlying morphisms. Apply the lower-shriek functor of f
to that square, paste it to base change, and paste the naturality square of the
change from the chosen compactification to c. Apply the full-subcategory inclusion
and paste the naturality of the comparison with the ambient lower shriek for c.
The two vertical composites are exactly the components defining `atNativePoint`. -/
theorem atNativePoint_naturality {N M : WeilSheaf k ℓ X} (g : N ⟶ M) :
    (pull (ℓ := ℓ) (S₀).hom).map (shriekImage.map g) ≫ (atNativePoint M).hom =
      (atNativePoint N).hom ≫ (rightDerivedLowerShriekOfCompactification Λ
        (WeilComplex.geometricFiberCompactification (k₀ := k) X)).map (carrier.map g).hom := by
  let f := WeilComplex.geometricFiberStructureMorphism (k₀ := k) X
  let c := WeilComplex.geometricFiberCompactification (k₀ := k) X
  let sq : IsPullback (𝟙 (Xbar).left) f.left (toPoint Xbar).left (S₀).hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, toPoint_left]; exact f.w.symm⟩
  let d : boundedConstructibleUpperStarOfMap ℓ (X := Xbar) (Y := Xbar) (𝟙 _) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((leftDerivedUpperStarId Λ _).app K.obj))
      (fun g ↦ ObjectProperty.hom_ext _ ((leftDerivedUpperStarId Λ _).hom.naturality g.hom))
  let j := boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
    (compactificationOverField f) c
  let t := boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c
  let v := carrier.map g
  let I := (boundedConstructible (condensedRingObj Λ (S₀).left)).ι
  let exchange := purityFieldLowerShriekBaseChange ℓ (toPoint Xbar) f sq
  let D := boundedConstructibleLowerShriek ℓ f
  let comparison (Z : WeilSheaf k ℓ X) :
      (pull (ℓ := ℓ) (S₀).hom).obj (shriekImage.obj Z) ⟶
        (rightDerivedLowerShriekOfCompactification Λ c).obj (carrier.obj Z).obj := I.map
    (exchange.hom.app (carrier.obj Z) ≫
      D.map (d.hom.app (carrier.obj Z)) ≫ j.hom.app (carrier.obj Z)) ≫ t.hom.app (carrier.obj Z)
  let idK (Z : WeilSheaf k ℓ X) := d.app (carrier.obj Z)
  let inner (Z : WeilSheaf k ℓ X) := exchange.app (carrier.obj Z) ≪≫
    D.mapIso (idK Z) ≪≫ j.app (carrier.obj Z)
  let full (Z : WeilSheaf k ℓ X) :
      (pull (ℓ := ℓ) (S₀).hom).obj (shriekImage.obj Z) ≅
        (rightDerivedLowerShriekOfCompactification Λ c).obj (carrier.obj Z).obj :=
    I.mapIso (inner Z) ≪≫ t.app (carrier.obj Z)
  have isoApp (Z : WeilSheaf k ℓ X) : atNativePoint Z = full Z := rfl
  have app (Z : WeilSheaf k ℓ X) : (atNativePoint Z).hom = comparison Z := by
    rw [isoApp]
    simp -implicitDefEqProofs only [full, inner, idK, comparison, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
  rw [app N, app M]
  have first := CommSq.mk (exchange.hom.naturality v)
  have second := CommSq.mk ((Functor.isoWhiskerRight d D).hom.naturality v)
  have third := CommSq.mk (j.hom.naturality v)
  have last := CommSq.mk (t.hom.naturality v)
  have inside := first.vert_comp (second.vert_comp third)
  have h := ((I.map_commSq inside).vert_comp last).w
  dsimp only [comparison, v, shriekImage, pull, I, Functor.comp_map, Functor.id_map,
    boundedConstructibleUpperStarOfMap, ObjectProperty.lift_map, ObjectProperty.ι_map,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at h ⊢
  exact h


private theorem nativeComparison_naturality {N M : WeilSheaf k ℓ X} (g : N ⟶ M) :
    (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor.map (WeilComplex.forget.map
        ((WeilComplex.derivedLowerShriek k ℓ aX).map (WeilSheaf.toComplex.map g))) ≫
      (nativeComparison M).hom =
    (nativeComparison N).hom ≫ (rightDerivedLowerShriekOfCompactification Λ
      (WeilComplex.geometricFiberCompactification (k₀ := k) X)).map (carrier.map g).hom := by
  let c := WeilComplex.structureMorphismCompactification (k₀ := k) X
  let h := comp_over aX (Spec (.of k))
  let Bf := (WeilComplex.derivedLowerShriek k ℓ aX).map (WeilSheaf.toComplex.map g)
  let F := (IsoAlgebra.forget (CondensedRing.lowerStar Λ
    (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)).mapDerivedCategory
  let e := Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso
    (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k))))
  let d := Functor.isoWhiskerRight (WeilComplex.derivedLowerShriekCompToCondensedIso k ℓ aX) F
  let j := weilRightDerivedLowerShriekCompForgetIso Λ c h
  let left (Z : WeilSheaf k ℓ X) := e.inv.app (B Z).obj
  let middle (Z : WeilSheaf k ℓ X) := d.hom.app (WeilSheaf.toComplex.obj Z)
  let right (Z : WeilSheaf k ℓ X) := j.hom.app
    ((ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj (WeilSheaf.toComplex.obj Z).obj)
  have app (Z : WeilSheaf k ℓ X) :
      (nativeComparison Z).hom = left Z ≫ middle Z ≫ right Z := by rfl
  rw [app, app]
  let mid₁ := F.map ((ProEtaleWeilSheaf.derivedEquivCondensed k ℓ (Spec (.of k))).functor.map Bf.hom)
  let mid₂ := F.map ((ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k ℓ aX c).map
    ((ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.map (WeilSheaf.toComplex.map g).hom))
  refine (CommSq.vert_comp (i := mid₁) ?_ (CommSq.vert_comp (i := mid₂) ?_ ?_)).w
  · exact ⟨e.inv.naturality Bf.hom⟩
  · exact ⟨d.hom.naturality (WeilSheaf.toComplex.map g)⟩
  · exact ⟨j.hom.naturality
      ((ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.map (WeilSheaf.toComplex.map g).hom)⟩

/-- Postcomposition in the geometric model gives the native compact-support cohomology map. -/
theorem evaluate_naturality {N M : WeilSheaf k ℓ X} (g : N ⟶ M) (i : ℤ)
    (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    evaluate M i (v ≫ shriekImage.map g) =
      WeilComplex.compactlySupportedCohomologyMap (WeilSheaf.toComplex.map g) i (evaluate N i v) := by
  let Bf := (WeilComplex.derivedLowerShriek k ℓ aX).map (WeilSheaf.toComplex.map g)
  let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
  let P := pull (ℓ := ℓ) (S₀).hom
  have hn := (CommSq.vert_comp ⟨atNativePoint_naturality g⟩
    (CommSq.vert_inv (g := nativeComparison N) (h := nativeComparison M)
      ⟨nativeComparison_naturality g⟩)).w
  have hr : nativeRepresentative M i (v ≫ shriekImage.map g) =
      nativeRepresentative N i v ≫ WeilComplex.forget.map Bf := by
    apply E.map_injective
    unfold nativeRepresentative
    rw [E.map_comp, E.map_preimage, E.map_preimage]
    let a := (singleUnit (ℓ := ℓ) (S₀).left i).hom
    let t := (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv
    refine (congrArg (fun y ↦ a ≫ t ≫ y ≫ (atNativePoint M).hom ≫ (nativeComparison M).inv)
      (P.map_comp v (shriekImage.map g))).trans ?_
    let b (K : WeilSheaf k ℓ X) := (atNativePoint K).hom ≫ (nativeComparison K).inv
    let bmap := E.map (WeilComplex.forget.map Bf)
    change a ≫ t ≫ (P.map v ≫ P.map (shriekImage.map g)) ≫ b M =
      (a ≫ t ≫ P.map v ≫ b N) ≫ bmap
    simp only [Category.assoc]
    exact congrArg (fun y ↦ a ≫ t ≫ P.map v ≫ y) hn
  let H := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
    ).mapDerivedCategoryHomologyFunctorIso i
  let m := ((WeilComplex.homologySheaf i).map Bf).hom.hom.f
  let z := DerivedCategory.homSingleToHomology (AdicSheaf.unit ℓ (S₀).left) i _
    (nativeRepresentative N i v)
  change nativeValue (B M) i (nativeRepresentative M i (v ≫ shriekImage.map g)) = _
  rw [show nativeRepresentative M i (v ≫ shriekImage.map g) = _ from hr]
  change globalSectionOfModHom (DerivedCategory.homSingleToHomology _ i _
    (nativeRepresentative N i v ≫ WeilComplex.forget.map Bf) ≫ H.inv.app _) =
    ((Sheaf.Γ _ _).map m.hom).hom (globalSectionOfModHom (z ≫ H.inv.app _))
  rw [DerivedCategory.homSingleToHomology_comp, Category.assoc]
  have hh : (DerivedCategory.homologyFunctor _ i).map (WeilComplex.forget.map Bf) ≫
      H.inv.app (B M).obj = H.inv.app (B N).obj ≫ m := H.inv.naturality Bf.hom
  refine (congrArg (fun y ↦ globalSectionOfModHom (z ≫ y)) hh).trans ?_
  exact (congrArg globalSectionOfModHom (Category.assoc z (H.inv.app (B N).obj) m).symm).trans
    (globalSectionOfModHom_comp _ m)

/-- Evaluation is additive on representatives. -/
theorem evaluate_add (N : WeilSheaf k ℓ X) (i : ℤ)
    (v w : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    evaluate N i (v + w) = evaluate N i v + evaluate N i w := by
  let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
  have add {A D} (a b : E.obj A ⟶ E.obj D) :
      E.preimage (a + b) = E.preimage a + E.preimage b :=
    E.map_injective (by simp)
  let P := pull (ℓ := ℓ) (S₀).hom
  let A := (singleUnit (ℓ := ℓ) (S₀).left i).hom
  let t := (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv
  let b := (atNativePoint N).hom ≫ (nativeComparison N).inv
  let U := AdicSheaf.unit ℓ (S₀).left
  let D := WeilComplex.forget.obj (B N)
  let H := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
    ).mapDerivedCategoryHomologyFunctorIso i
  let r (x : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :=
    E.preimage (A ≫ t ≫ P.map x ≫ b)
  have hr : r (v + w) = r v + r w := by
    dsimp only [r]
    exact (congrArg (fun x ↦ E.preimage (A ≫ t ≫ x ≫ b)) (P.map_add (f := v) (g := w))).trans
      ((congrArg E.preimage (((Preadditive.leftComp _ A).comp ((Preadditive.leftComp _ t).comp
        (Preadditive.rightComp _ b))).map_add (P.map v) (P.map w))).trans (add _ _))
  let m (x : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :=
    DerivedCategory.homSingleToHomology U i D (r x) ≫ H.inv.app (B N).obj
  have hm : m (v + w) = m v + m w := by
    dsimp only [m, DerivedCategory.homSingleToHomology]
    rw [hr, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  change globalSectionOfModHom (m (v + w)) = globalSectionOfModHom (m v) + globalSectionOfModHom (m w)
  exact (congrArg globalSectionOfModHom hm).trans (globalSectionOfModHom_add _ _)

/-- At the native point, scalar multiplication on the shifted tensor unit transports to
multiplication by the same scalar on the native single regular module, using the
identification prescribed in `evaluate`. -/
theorem nativeSingle_scalar (i : ℤ) (c : PadicAlgCl ℓ) :
    let p := (S₀).hom
    let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
    let a := (singleUnit (ℓ := ℓ) (S₀).left i).hom ≫ (pullUnit (ℓ := ℓ) p (-i)).inv
    let s := AdicSheaf.smul (ULift.up c) (AdicSheaf.unit ℓ (S₀).left)
    E.map ((DerivedCategory.singleFunctor _ i).map s) ≫ a =
      a ≫ (pull (ℓ := ℓ) p).map ((shiftFunctor _ (-i)).map (pointScalar ℓ Ω c).asHom) := by
  exact WeilII.shiftedUnitScalarTransport ℓ Ω (S₀).hom i c
    (singleUnit (ℓ := ℓ) (S₀).left i ≪≫ (pullUnit (ℓ := ℓ) (S₀).hom (-i)).symm)

private theorem nativeValue_smul (D : WeilComplex k ℓ (Spec (.of k))) (i : ℤ)
    (w : (DerivedCategory.singleFunctor _ i).obj (AdicSheaf.unit ℓ (S₀).left) ⟶
      WeilComplex.forget.obj D) (c : PadicAlgCl ℓ) :
    nativeValue D i ((DerivedCategory.singleFunctor _ i).map
      (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit ℓ (S₀).left)) ≫ w) =
      c • nativeValue D i w := by
  let U := AdicSheaf.unit ℓ (S₀).left
  let s := AdicSheaf.smul (ULift.up c) U
  let F := DerivedCategory.homologyFunctor (AdicSheaf ℓ (S₀).left) i
  let t := DerivedCategory.singleFunctorCompHomologyFunctorIso (AdicSheaf ℓ (S₀).left) i
  let h := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
    ).mapDerivedCategoryHomologyFunctorIso i
  let v := t.inv.app U ≫ F.map w ≫ h.inv.app D.obj
  have hs : t.inv.app U ≫ F.map ((DerivedCategory.singleFunctor _ i).map s) =
      s ≫ t.inv.app U := (t.inv.naturality s).symm
  have he : (t.inv.app U ≫ F.map ((DerivedCategory.singleFunctor _ i).map s ≫ w)) ≫
      h.inv.app D.obj = s ≫ v := by
    rw [F.map_comp, Category.assoc, Category.assoc, reassoc_of% hs]
  unfold nativeValue DerivedCategory.homSingleToHomology
  change globalSectionOfModHom ((t.inv.app U ≫ F.map (_ ≫ w)) ≫ h.inv.app D.obj) =
    (ULift.up.{u+1} c) • globalSectionOfModHom ((t.inv.app U ≫ F.map w) ≫ h.inv.app D.obj)
  rw [he, Category.assoc, AdicSheaf.smul_comp]
  exact adicGlobalSectionOfHom_comp_smul v c

/-- Evaluation respects the scalar action by precomposition on the shifted tensor unit. -/
theorem evaluate_smul (N : WeilSheaf k ℓ X) (i : ℤ) (c : PadicAlgCl ℓ)
    (x : (gradedHom ℓ Ω (-i)).obj (shriekImage.obj N)) :
    evaluate N i (gradedHomHom ℓ Ω (c • x)) = c • evaluate N i (gradedHomHom ℓ Ω x) := by
  let P := pull (ℓ := ℓ) (S₀).hom
  let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
  let a := (singleUnit (ℓ := ℓ) (S₀).left i).hom
  let t := (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv
  let b := (atNativePoint N).hom ≫ (nativeComparison N).inv
  let s := (DerivedCategory.singleFunctor _ i).map
    (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit ℓ (S₀).left))
  let q := (shiftFunctor _ (-i)).map (pointScalar ℓ Ω c).asHom
  let v := gradedHomHom ℓ Ω x
  have h : nativeRepresentative N i (q ≫ v) = s ≫ nativeRepresentative N i v := by
    apply E.map_injective
    unfold nativeRepresentative
    rw [E.map_comp, E.map_preimage, E.map_preimage]
    change a ≫ t ≫ P.map (q ≫ v) ≫ b = E.map s ≫ a ≫ t ≫ P.map v ≫ b
    have hs : E.map s ≫ (a ≫ t) = (a ≫ t) ≫ P.map q := nativeSingle_scalar i c
    refine (congrArg (fun y ↦ a ≫ t ≫ y ≫ b) (P.map_comp q v)).trans ?_
    calc
      _ = ((a ≫ t) ≫ P.map q) ≫ P.map v ≫ b := by
        simp only [Category.assoc]
        exact congrArg (fun y ↦ a ≫ t ≫ y) (Category.assoc (P.map q) (P.map v) b)
      _ = (E.map s ≫ (a ≫ t)) ≫ P.map v ≫ b :=
        congrArg (fun x ↦ x ≫ P.map v ≫ b) hs.symm
      _ = _ := by simp only [Category.assoc]
  change nativeValue (B N) i (nativeRepresentative N i (q ≫ v)) = _
  exact (congrArg (nativeValue (B N) i) h).trans (nativeValue_smul _ i _ c)

/-- Evaluation at the regular generator identifies shifted-unit maps with compactly
supported cohomology in every degree, for any Weil sheaf. -/
def evaluationLinearEquiv (N : WeilSheaf k ℓ X) (i : ℤ) :
    (gradedHom ℓ Ω (-i)).obj (shriekImage.obj N) ≃ₗ[PadicAlgCl ℓ]
      (N.compactlySupportedCohomology i).carrier :=
  LinearEquiv.ofBijective
    { toFun := fun x ↦ evaluate N i (gradedHomHom ℓ Ω x)
      map_add' := fun x y ↦ evaluate_add N i (gradedHomHom ℓ Ω x) (gradedHomHom ℓ Ω y)
      map_smul' := evaluate_smul N i } (evaluate_bijective N i)

/-- The sheaf morphism whose value on one defines evaluation. -/
def sectionHom (N : WeilSheaf k ℓ X) (i : ℤ) (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    𝟙_ (Sheaf (Scheme.ProEt.topology (S₀).left) (WeilCoefficients.{u} ℓ)) ⟶
      ((WeilComplex.homologySheaf i).obj (B N)).obj.carrier.X :=
  let F := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))
  MonObj.one (X := adicConstantSheaf ℓ (S₀).left) ≫
    (DerivedCategory.homSingleToHomology _ i _ (nativeRepresentative N i v) ≫
      (F.mapDerivedCategoryHomologyFunctorIso i).inv.app (B N).obj).hom

/-- The four shifted-unit comparisons for a commutative square agree after
transport along derived pullback exchange. -/
theorem pullUnit_square {X₁ Y₁ Y₂ X₂ : Scheme.{u}} {p : X₁ ⟶ Y₁} {g : Y₂ ⟶ Y₁}
    {p' : X₂ ⟶ Y₂} {g' : X₂ ⟶ X₁} (sq : CommSq g' p' p g) (n : ℤ) :
    (pullbackSquareComparison Λ sq).hom.app _ ≫
      (pull (ℓ := ℓ) g').map (pullUnit (ℓ := ℓ) p n).hom ≫ (pullUnit (ℓ := ℓ) g' n).hom =
      (pull (ℓ := ℓ) p').map (pullUnit (ℓ := ℓ) g n).hom ≫ (pullUnit (ℓ := ℓ) p' n).hom := by
  have h := WeilII.pullbackSquare_shiftedUnit Λ sq n
  dsimp only [pullUnit, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h ⊢
  transport_compactification_component h

/-- Frobenius exchange along the projection of the native geometric point. The two
pullback paths agree by the Frobenius square for the second projection. At the
native point, pullback is identified with pushforward along inverse Frobenius. -/
def pointFrobeniusExchange :
    pull (ℓ := ℓ) (S₀).hom ⋙ (CondensedRing.lowerStar Λ
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory ≅
      pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom ⋙ pull (ℓ := ℓ) (S₀).hom :=
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let t := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ σ)
  let sq : CommSq σ.hom (S₀).hom (S₀).hom (specGeometricFrobenius k).asIso.hom :=
    ⟨(Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
  Functor.isoWhiskerLeft _ t.symm ≪≫ (pullbackSquareComparison Λ sq).symm

/-- The coefficient identification of the native single regular module intertwines
inverse Frobenius pushforward with the shifted-unit datum in pullback coordinates.

Source: `SmoothPurityConstantWeilDatum.purity_adicLowerStarUnit_condensed`,
`UpperStarUnitCoherence`, and the comparison of singles with shifts for exact
derived functors. In degree zero the regular-module isomorphism for inverse
pushforward is the inverse of the coefficient ring map. The model equivalence
identifies it with the condensed unit datum through the pullback/pushforward
isomorphism, by the cited coefficient formula. Apply the single functor to that
square, using its naturality for composition of exact functors and their natural
isomorphisms. On the derived tensor unit, the pullback unit is the left-derived
counit followed by the single of the ordinary monoidal unit map. The comparison
between the single of the ordinary unit and the derived unit carries the former
square to this normalization. Shift by minus i. The shift comparisons commute
with the coefficient and pullback isomorphisms, and the shift-to-single comparison
for the two exact functors identifies their singles in degree i. This gives the
square for the specified `singleUnit`. -/
theorem singleUnit_native_frobenius (i : ℤ) :
    let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
    let F := WeilSheaf.frobeniusPullback k ℓ (Spec (.of k))
    let U := AdicSheaf.unit ℓ (S₀).left
    let u := (F.mapDerivedCategorySingleFunctor i).app U ≪≫
      (DerivedCategory.singleFunctor _ i).mapIso (adicLowerStarUnitIso ℓ σ.symm)
    let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
    let c := IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k)))
    let t := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ σ)
    IsWeilEquivariant (CondensedRing.lowerStar Λ σ.inv).mapDerivedCategory
      (transportWeilDatum E c.symm u.hom) (t.inv.app _ ≫ (pullUnit (ℓ := ℓ) σ.hom (-i)).hom)
      (singleUnit (ℓ := ℓ) (S₀).left i).hom := by
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  have h := WeilII.singleUnitWeilDatum ℓ σ i
  exact h

/-- The shifted source comparison respects the geometric and native unit data.
Source: `UpperStarUnitCoherence`, `SmoothPurityConstantWeilDatum`, and the
shift and single comparisons of exact derived functors.

At degree zero, use the formula for the pullback compositor at the tensor unit on
each side of the projection square. Both compositions identify pullback of the unit
along the same scheme map with the unit. On the native side the comparison between
pullback and inverse pushforward carries the inverse-pushforward regular-module
isomorphism to the pullback unit. The coefficient equivalence carries it to the
condensed unit by `purity_adicLowerStarUnit_condensed`. Taking singles respects both
the transformation of exact functors and their composition. Transport that equality
from degree zero to degree i by the single-functor shift isomorphism. Each pullback
comparison commutes with shift, giving exactly the two factors of `singleUnit`
and the two shifted-unit constraints along the Frobenius and the projection. -/
theorem singleUnit_frobenius (i : ℤ) :
    let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
    let F := WeilSheaf.frobeniusPullback k ℓ (Spec (.of k))
    let U := AdicSheaf.unit ℓ (S₀).left
    let u := (F.mapDerivedCategorySingleFunctor i).app U ≪≫
      (DerivedCategory.singleFunctor _ i).mapIso (adicLowerStarUnitIso ℓ σ.symm)
    let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
    let c := IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k)))
    IsWeilEquivariant (CondensedRing.lowerStar Λ σ.inv).mapDerivedCategory
      (transportWeilDatum E c.symm u.hom)
      (transportWeilDatum (pull (ℓ := ℓ) (S₀).hom) (pointFrobeniusExchange (ℓ := ℓ) (k := k)).symm
        (pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)).hom)
      ((singleUnit (ℓ := ℓ) (S₀).left i).hom ≫ (pullUnit (ℓ := ℓ) (S₀).hom (-i)).inv) := by
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let P := pull (ℓ := ℓ) (S₀).hom
  let H := (CondensedRing.lowerStar Λ σ.inv).mapDerivedCategory
  let t := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ σ)
  let g := (specGeometricFrobenius k).asIso.hom
  let sq : CommSq σ.hom (S₀).hom (S₀).hom g :=
    ⟨(Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure⟩
  let d := pullbackSquareComparison Λ sq
  let a := pullUnit (ℓ := ℓ) (S₀).hom (-i)
  let s := pullUnit (ℓ := ℓ) g (-i)
  let v := pullUnit (ℓ := ℓ) σ.hom (-i)
  have q := WeilII.equivariant_of_pullback_square P (pull (ℓ := ℓ) g)
    (pull (ℓ := ℓ) σ.hom) H t d s.hom a.hom v.hom (pullUnit_square (ℓ := ℓ) sq (-i))
  have ex : pointFrobeniusExchange (k := k) (ℓ := ℓ) =
      Functor.isoWhiskerLeft P t.symm ≪≫ d.symm := rfl
  have invq := IsWeilEquivariant.inv H a q
  have comp := (singleUnit_native_frobenius (k := k) (ℓ := ℓ) i).comp invq
  rw [← ex] at comp
  exact comp

/-- The geometric comparison into the arithmetic compactification respects the
two geometric Frobenius actions. Source: `CondensedModelBaseChange` and
`geometricCompactificationFrobeniusRefinement`.

Compute the exchange on the compactification obtained by taking the geometric
fibre of the arithmetic compactification. Its middle scheme carries the lift of
Frobenius. In the open square, restriction exchange is the mate of the equality
of the two composites of pushforwards along the commuting isomorphism square.
Its left mate is extension-by-zero exchange. In the proper square, the right
mate of the pullback square is the canonical exchange of the direct images.
Identify pullback by each Frobenius with pushforward by its inverse and apply the
exact or right-derived comparison to the respective mate. The composite then
acts by the open and proper exchanges defining `compactifiedWeilFrobenius`.
The base change from the geometric point by its second projection commutes with
these two exchanges by pasting their squares, since the second projection is
equivariant. Finally transport from the pulled-back arithmetic compactification
to the chosen Nagata one by the normalized refinement square. Its two comparison
maps cancel with those in `atNativePoint` and `imageFrobenius`. -/
theorem atNativePoint_frobenius (N : WeilSheaf k ℓ X) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let M := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj (WeilSheaf.toComplex.obj N).obj
    IsWeilEquivariant (CondensedRing.lowerStar Λ
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory
      (transportWeilDatum (pull (ℓ := ℓ) (S₀).hom) (pointFrobeniusExchange (ℓ := ℓ) (k := k)).symm
        (imageFrobenius N).hom)
      (WeilII.compactifiedWeilFrobenius Λ C (comp_over aX (Spec (.of k))) M)
      (atNativePoint N).hom := by
  intro C M
  let K := carrier.obj N
  let v := carrierFrobenius N
  let w := (IsoAlgebra.derivedStrIso _).hom.app M
  let sx := NativePointShriek.inversePush (ℓ := ℓ) (aX).geometricGaloisFrobenius.asIso
  have hv : sx.hom.app K.obj ≫ w = v.hom.hom := Category.assoc _ _ _
  let dst := compactifiedWeilFrobenius Λ C (comp_over aX (Spec (.of k))) M
  have factor := compactifiedWeilFrobenius_factor Λ C (comp_over aX (Spec (.of k))) M
  have square := NativePointShriek.coefficientFrobenius K v w hv dst (by exact_by_kernel factor)
  exact_by_kernel square

/-- The native coefficient comparison carries descent to the open and proper
exchanges of the arithmetic compactification. -/
theorem nativeComparison_frobenius (N : WeilSheaf k ℓ X) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let M := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj (WeilSheaf.toComplex.obj N).obj
    let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
    let c := IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k)))
    IsWeilEquivariant (CondensedRing.lowerStar Λ
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv).mapDerivedCategory
      (transportWeilDatum E c.symm ((IsoAlgebra.derivedStrIso _).hom.app (B N).obj))
      (WeilII.compactifiedWeilFrobenius Λ C (comp_over aX (Spec (.of k))) M)
      (nativeComparison N).hom := by
  let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
  let M := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ X).functor.obj (WeilSheaf.toComplex.obj N).obj
  let b := ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k))
  let H := CondensedRing.lowerStar Λ (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
  let f := (WeilComplex.derivedLowerShriekCompToCondensedIso k ℓ aX).hom.app (WeilSheaf.toComplex.obj N)
  have eq : WeilComplex.condensedCarrierIso (B N).obj = (IsoAlgebra.derivedExactForgetCommIso b).app (B N).obj := by
    simp only [WeilComplex.condensedCarrierIso, Functor.mapDerivedCategoryCompForgetIso,
      IsoAlgebra.derivedExactForgetCommIso, Iso.trans_assoc, b]
  have h₁ := IsWeilEquivariant.inv H.mapDerivedCategory ((IsoAlgebra.derivedExactForgetCommIso b).app (B N).obj)
    (IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app b (B N).obj)
  have h₂ : IsWeilEquivariant H.mapDerivedCategory ((IsoAlgebra.derivedStrIso H).hom.app _)
      ((IsoAlgebra.derivedStrIso H).hom.app _) ((IsoAlgebra.forget H).mapDerivedCategory.map f) :=
    (IsoAlgebra.derivedStrIso H).hom.naturality f
  have h₃ := WeilII.compactifiedWeilFrobenius_forget Λ C (comp_over aX (Spec (.of k))) M
  unfold nativeComparison
  rw [eq]
  exact h₁.comp (h₂.comp h₃)

/-- Native descent of a compact-support representative, before taking homology.

Source: the two factors of compact-support exchange in `CondensedModelBaseChange`,
the forgetful comparison in `SmoothPurityShriekWeilUniversality`, and the normalized
refinement square in `geometricCompactificationFrobeniusRefinement`.

Apply the faithful derived coefficient equivalence. The projection from the native
point commutes with geometric Frobenius, hence pullback of the Frobenius transform
is conjugation of the pulled-back map by the two components of the pullback square.
On the source, the inverse-pushforward constraint on the regular module is the
coefficient ring isomorphism and the coefficient equivalence carries it to the
pullback-unit constraint. Shift compatibility carries this equality to degree i.
On the target, use the compactification obtained from the arithmetic one. Forgetting
extension by zero gives the left mate of the restriction square, and forgetting
proper direct image gives the right mate of the pullback square. These are the two
factors of geometric compactification exchange. Transport to the chosen compactification
by the normalized refinement square and compose with the Weil coefficient comparison.
Pasting the source and target squares with naturality on the representative gives
the indicated conjugate after cancelling the coefficient equivalence. -/
theorem nativeRepresentative_frobenius (N : WeilSheaf k ℓ X) (i : ℤ)
    (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    let F := WeilSheaf.frobeniusPullback k ℓ (Spec (.of k))
    let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
    let U := AdicSheaf.unit ℓ (S₀).left
    nativeRepresentative N i ((pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)).inv ≫
      (pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom).map v ≫ (imageFrobenius N).hom) =
      (DerivedCategory.singleFunctor _ i).map (adicLowerStarUnitIso ℓ σ.symm).inv ≫
        (F.mapDerivedCategorySingleFunctor i).inv.app U ≫
        F.mapDerivedCategory.map (nativeRepresentative N i v) ≫
        (IsoAlgebra.derivedStrIso F).hom.app (B N).obj := by
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let F := WeilSheaf.frobeniusPullback k ℓ (Spec (.of k))
  let H := (CondensedRing.lowerStar Λ σ.inv).mapDerivedCategory
  let E := (adicSheafDerivedEquivCondensedMod ℓ (S₀).left).functor
  let P := pull (ℓ := ℓ) (S₀).hom
  let U := AdicSheaf.unit ℓ (S₀).left
  let c := IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ (Spec (.of k)))
  let u := (F.mapDerivedCategorySingleFunctor i).app U ≪≫
    (DerivedCategory.singleFunctor _ i).mapIso (adicLowerStarUnitIso ℓ σ.symm)
  have h := WeilII.preimage_conjugate_descent F.mapDerivedCategory _ H E P c
    (pointFrobeniusExchange (k := k) (ℓ := ℓ)) u ((IsoAlgebra.derivedStrIso F).hom.app (B N).obj)
    (pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)) (imageFrobenius N).hom
    _ _ (singleUnit_frobenius (k := k) (ℓ := ℓ) i)
    ((atNativePoint_frobenius N).comp (IsWeilEquivariant.inv H _ (nativeComparison_frobenius N))) v
  simp only [u, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at h
  unfold nativeRepresentative
  exact_mod_proofs h

/-- Frobenius descent for the comparison of the two compactifications on a representative.
Source: the open and proper squares in `CondensedModelBaseChange`, the two derived
forgetful squares in `IsoAlgebra`, and compactification refinement as in
`geometricCompactificationFrobeniusRefinement`.

For the compactification obtained from the arithmetic one, forget the Weil structure
on extension by zero and proper direct image in order. The first exchange transposes
the square for open restriction and the second transposes the square for direct image.
Identifying pullback by Frobenius with inverse pushforward takes these transposes to
the open and proper factors of geometric base change. Paste the two squares and the
Weil-model comparison. For the chosen geometric compactification, paste this square
with the refinement square and cancel inverse comparisons. This gives the same square
for `atNativePoint` followed by the inverse `nativeComparison`. The second projection
of the native point intertwines the two Frobenius maps. Transport the representative
through this square, and take degree i homology. Exactness of the Frobenius equivalence
identifies the resulting structure with the one on the native homology sheaf.
The pullback unit and shift comparisons carry the single regular generator to the
single regular generator. On the underlying sheaf this is the monoidal unit map of the
inverse pushforward, since the comparison of coefficient rings preserves one. -/
theorem sectionHom_frobenius (N : WeilSheaf k ℓ X) (hN : N.IsLisse) (i : ℤ)
    (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    let G := ProEtale.lowerStar (WeilCoefficients.{u} ℓ)
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
    sectionHom N i ((pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)).inv ≫
      (pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom).map v ≫ (imageFrobenius N).hom) =
      Functor.LaxMonoidal.ε G ≫ G.map (sectionHom N i v) ≫
        ((WeilComplex.homologySheaf i).obj (B N)).obj.str.hom.hom := by
  clear hN
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let F := WeilSheaf.frobeniusPullback k ℓ (Spec (.of k))
  let G := ProEtale.lowerStar (WeilCoefficients.{u} ℓ) σ.inv
  let U := AdicSheaf.unit ℓ (S₀).left
  let m := (adicLowerStarUnitIso ℓ σ.symm).inv
  let h := (IsoAlgebra.forget F).mapDerivedCategoryHomologyFunctorIso i
  let w := nativeRepresentative N i v
  let e := DerivedCategory.homSingleToHomology U i _ w ≫ h.inv.app (B N).obj
  let K := ((WeilComplex.homologySheaf i).obj (B N)).obj
  let η := MonObj.one (X := adicConstantSheaf ℓ (S₀).left)
  have hη : η ≫ m.hom = Functor.LaxMonoidal.ε G ≫ G.map η :=
    IsMonHom.one_hom (f := adicConstantSheafToLowerStar ℓ σ.inv)
  unfold sectionHom
  rw [nativeRepresentative_frobenius N i v]
  have hd := WeilII.homSingleToHomology_descent F U m (B N).obj i w
  refine (congrArg (fun j ↦ η ≫ j.hom) hd).trans ?_
  change η ≫ (m.hom ≫ G.map e.hom ≫ K.str.hom.hom) =
    Functor.LaxMonoidal.ε G ≫ G.map (η ≫ e.hom) ≫ K.str.hom.hom
  rw [G.map_comp, ← Category.assoc η, hη]
  exact Category.assoc _ _ _

private theorem evaluate_frobenius (N : WeilSheaf k ℓ X) (hN : N.IsLisse) (i : ℤ)
    (v : shiftedUnit ℓ Ω (-i) ⟶ shriekImage.obj N) :
    evaluate N i ((pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)).inv ≫
      (pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom).map v ≫ (imageFrobenius N).hom) =
      (N.compactlySupportedCohomology i).frobenius (evaluate N i v) := by
  let K := (WeilComplex.homologySheaf i).obj (B N)
  let σ := (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
  let G := ProEtale.lowerStar (WeilCoefficients.{u} ℓ) σ
  let e := (globalSectionsLowerStarIso (WeilCoefficients.{u} ℓ) σ).app K.obj.carrier.X
  let η := sectionHom N i v
  let θ := Functor.LaxMonoidal.ε G ≫ G.map η
  have hθ : globalSectionOfHom θ = e.inv.hom (globalSectionOfHom η) := by
    have hh : e.hom.hom (globalSectionOfHom θ) = globalSectionOfHom η :=
      globalSectionsLowerStarIso_hom_app_globalSectionOfHom σ η
    rw [← hh, ← ModuleCat.comp_apply, e.hom_inv_id, ModuleCat.id_apply]
  change globalSectionOfHom (sectionHom N i _) =
    ((Sheaf.Γ _ _).map K.obj.str.hom.hom).hom (e.inv.hom (globalSectionOfHom η))
  refine (congrArg globalSectionOfHom (sectionHom_frobenius N hN i v)).trans ?_
  refine (congrArg globalSectionOfHom (Category.assoc _ _ _).symm).trans ?_
  exact (globalSectionOfHom_comp θ K.obj.str.hom.hom).trans (congrArg _ hθ)

/-- Compactly supported classes have normalized, natural, Frobenius-equivariant shifted-unit
representatives. Source: Zhang, p. 2, in the argument from Proposition 1.5 to Theorem 1.1.
The coefficient and cohomology models are those of `WeilSheaf.Cohomology` and
`TraceFormula.PointTrace`.

Proof. For the arithmetic compact-support image of the degree-zero Weil sheaf, forget
the Weil structure, apply the exact coefficient equivalence, and use
`derivedLowerShriekCompToCondensedIso` followed by `weilRightDerivedLowerShriekCompForgetIso`.
This identifies its geometric carrier with extension by zero followed by proper direct
image for the geometrically pulled-back arithmetic compactification. The second projection
from the geometric fiber of the arithmetic point to the spectrum of the algebraic closure
is an isomorphism. Pull a representative back along it. Compact-support base change and
the comparison of compactifications give precisely the map in `atNativePoint`.

At the geometric point the condensed regular module is projective. Hence taking degree
`i` cohomology identifies maps from its single complex in degree `i` with maps from the
regular module to the cohomology object. Via the exact coefficient equivalence and its
unit isomorphism these are maps from the native regular module. Evaluation at its unit
section is a bijection onto the native sections defining compactly supported cohomology.
The resulting bijection is `evaluate`. Precomposing with multiplication by a constant
scalar multiplies the value at one by that scalar, by the coefficient equivalence's
unit-scalar formula. All the comparisons commute with postcomposition, giving naturality.

For the arithmetic compactification, forgetting the Weil structure on extension by zero
gives the open exchange followed by extension of the input structure. For the proper
factor it gives derived base change followed by pushforward of that structure. The open
exchange is determined by adjunction; the proper exchange is the mate of the pullback
comparison. Under geometric Frobenius these are the two factors defining compact-support
base change. Its compatibility with refinement transports the identification to the chosen
geometric compactification. Finally exact pullback commutes with cohomology and its unit
constraint carries one to one. Thus evaluating a pulled-back morphism, precomposed with
the inverse shifted-unit constraint and followed by the image Weil structure, gives the
native Frobenius on sections. Inverting the evaluation bijection gives the three formulas. -/
theorem exists_natural_equiv (i : ℤ) :
    ∃ ρ : ∀ (N : WeilSheaf k ℓ X), N.IsLisse →
        (N.compactlySupportedCohomology i).carrier ≃ₗ[PadicAlgCl ℓ]
          (gradedHom ℓ Ω (-i)).obj (shriekImage.obj N),
      (∀ N h u, (ρ N h).symm u = evaluate N i (gradedHomHom ℓ Ω u)) ∧
      (∀ (N M : WeilSheaf k ℓ X) (hN : N.IsLisse) (hM : M.IsLisse) (f : N ⟶ M) x,
        ρ M hM (WeilComplex.compactlySupportedCohomologyMap (WeilSheaf.toComplex.map f) i x) =
          (gradedHom ℓ Ω (-i)).map (shriekImage.map f) (ρ N hN x)) ∧
      (∀ N h x, gradedHomHom ℓ Ω (ρ N h ((N.compactlySupportedCohomology i).frobenius x)) =
        (pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-i)).inv ≫
        (pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom).map
          (gradedHomHom ℓ Ω (ρ N h x)) ≫ (imageFrobenius N).hom) := by
  let E (N : WeilSheaf k ℓ X) := evaluationLinearEquiv N i
  refine ⟨fun N _ ↦ (E N).symm, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro N M _ _ g x
    obtain ⟨u, rfl⟩ := (E N).surjective x
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    exact (evaluate_naturality g i (gradedHomHom ℓ Ω u)).symm
  · intro N h x
    obtain ⟨u, rfl⟩ := (E N).surjective x
    rw [LinearEquiv.symm_apply_apply]
    apply (evaluate_bijective N i).injective
    exact ((E N).apply_symm_apply _).trans (evaluate_frobenius N h i _).symm

end WeilII.CompactSupportClasses
