module

public import WeilII.AlgebraicGeometry.CompactifiedWeilFrobenius
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
import WeilII.AlgebraicGeometry.ChosenComparisonViaComponents
import WeilII.AlgebraicGeometry.FieldExchangeOfExact
import WeilII.AlgebraicGeometry.NativePointArithmeticCore
meta import WeilConjectures.Tactic.ExactByKernel
meta import WeilII.Tactic.SchemeComponentCongruence

/-! # Compactification exchange before evaluating the coefficient Weil structure -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
/-- Paste two equivariant morphisms across an inclusion functor, in the coordinates
of the isomorphisms before applying the inclusion. -/
theorem pasteEquivariantIsoComponents {C D : Type*} [Category* C] [Category* D]
    (I : C ⥤ D) (V : D ⥤ D) {A B E F : C} {W : D}
    (a : A ≅ B) (b : B ≅ E) (j : E ≅ F) (z : I.obj F ≅ W)
    (src : V.obj (I.obj A) ⟶ I.obj A) (mid : V.obj (I.obj E) ⟶ I.obj E)
    (dst dst' : V.obj W ⟶ W) (hdst : dst = dst')
    (front : IsWeilEquivariant V src mid (I.map (a.hom ≫ b.hom)))
    (back : IsWeilEquivariant V mid dst' (I.map j.hom ≫ z.hom)) :
    IsWeilEquivariant V src dst (I.mapIso (a ≪≫ b ≪≫ j) ≪≫ z).hom := by
  subst dst'
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    using front.comp back

section Compactification

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)

/-- The open and proper exchanges act on an arbitrary underlying geometric complex. -/
def compactificationInverseFrobeniusComponent
    (K : DerivedCategory (CategoryTheory.Mod _ (condensedRingObj Λ s.geometricFiber))) :
    (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).obj K) ⟶
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).obj
      ((lowerStar Λ s.geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj K) :=
  let ej := openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h)
  let ep := lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = c.g ≫ t)
  let R := (lowerStar Λ (Scheme.Hom.geometricFiberMap c.g (rfl : c.g ≫ t = c.g ≫ t))).rightDerivedFunctor
  (IsoAlgebra.derivedCommIso ep).hom.app _ ≫ R.map ((IsoAlgebra.derivedExactCommIso ej).hom.app K)

/-- The Weil datum is obtained by applying compactified direct image to the input descent
after the exchange on its underlying complex. This is functoriality of the proper factor. -/
theorem compactifiedWeilFrobenius_factor
    (M : DerivedCategory (IsoAlgebra (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv))) :
    compactifiedWeilFrobenius Λ c h M = compactificationInverseFrobeniusComponent Λ c h
      ((IsoAlgebra.forget _).mapDerivedCategory.obj M) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).map
        ((IsoAlgebra.derivedStrIso _).hom.app M) := by
  let ej := CondensedRing.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h)
  let ep := CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = c.g ≫ t)
  let K := (IsoAlgebra.forget _).mapDerivedCategory.obj M
  let J := (CondensedRing.openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h))).mapDerivedCategory
  let R := (CondensedRing.lowerStar Λ (Scheme.Hom.geometricFiberMap c.g (rfl : c.g ≫ t = c.g ≫ t))).rightDerivedFunctor
  let p := (IsoAlgebra.derivedCommIso ep).hom.app (J.obj K)
  let j := (IsoAlgebra.derivedExactCommIso ej).hom.app K
  let v := J.map ((IsoAlgebra.derivedStrIso _).hom.app M)
  exact (congrArg (p ≫ ·) (R.map_comp j v)).trans (Category.assoc p (R.map j) (R.map v)).symm

private theorem namedArithmeticExchange (K : DerivedCategory
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u+1}) (condensedRingObj Λ s.geometricFiber))) :
    let d := c.geometricFiber h
    let R := CondensedRing.rightDerivedLowerShriekOfCompactification Λ d
    let hi := (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap c.i (c.i_comp_g_comp h)).flip
    let hg := Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap c.g (rfl : c.g ≫ t = _)
    haveI : @WeaklyEtale d.Z d.Z (c.g ≫ t).geometricGaloisFrobenius.asIso.hom :=
      MorphismProperty.of_isPullback hg.flip (inferInstance : WeaklyEtale t.geometricGaloisFrobenius.asIso.hom)
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)).hom.app (R.obj K) ≫
      compactificationInverseFrobeniusComponent Λ c h K =
      (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ d d hi hg).hom.app K ≫
        R.map ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)).hom.app K) := by
  dsimp only [compactificationInverseFrobeniusComponent]
  exact_by_kernel arithmeticExactCompactification Λ c h K

end Compactification

namespace NativePointShriek

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]

set_option quotPrecheck false
local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "aX" => X ↘ Spec (CommRingCat.of k)
local notation "Xbar" => Over.mk (Scheme.Hom.geometricFiberToAlgebraicClosure aX)

private instance closureCharPrime : Fact (ringChar Ω).Prime :=
  ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩

/-- The residue characteristic stays distinct from the coefficient prime after base change. -/
private instance closureCharNe : Fact (ringChar Ω ≠ ℓ) :=
  ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

local notation "S₀" => WeilComplex.pointGeometricFiberOver k

local notation "f₀" => WeilComplex.geometricFiberStructureMorphism (k₀ := k) X
local notation "c₀" => WeilComplex.geometricFiberCompactification (k₀ := k) X
local notation "R₀" => CondensedRing.rightDerivedLowerShriekOfCompactification Λ c₀
local notation "Iₓ" => (boundedConstructible (condensedRingObj Λ (Xbar).left)).ι
local notation "Iₛ" => (boundedConstructible (condensedRingObj Λ (S₀).left)).ι
local notation "H₀" => boundedConstructibleLowerShriek ℓ f₀
local notation "σₓ" => (aX).geometricGaloisFrobenius.asIso
local notation "σₛ" => (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "Fₓ" => boundedConstructibleUpperStarOfMap ℓ (X := Xbar) (Y := Xbar) (σₓ).hom

/-- Compare the chosen compactification of the native structure map with its arithmetic
compactification, on all bounded constructible morphisms. -/
def changeCompactification : H₀ ⋙ Iₛ ≅ Iₓ ⋙ R₀ :=
  Functor.isoWhiskerRight
    (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (compactificationOverField f₀) c₀)
    Iₛ ≪≫ boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c₀

/-- Pullback along an isomorphism equals exact pushforward along its inverse. -/
def inversePush {S T : Scheme.{u}} (e : S ≅ T) :
    (CondensedRing.upperStar Λ e.hom).leftDerivedFunctor ≅ (CondensedRing.lowerStar Λ e.inv).mapDerivedCategory :=
  leftDerivedUpperStarIsoMapDerivedCategory Λ e.hom ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ e)

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
private theorem arithmeticAmbient (K : Dᵇc((Xbar).left)⟦Λ⟧) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let h := comp_over aX (Spec (.of k))
    let hi := (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap C.i (C.i_comp_g_comp h)).flip
    let hg := Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap C.g
      (rfl : C.g ≫ (Spec (.of k) ↘ Spec (.of k)) = _)
    haveI : @WeaklyEtale (c₀).Z (c₀).Z
        (C.g ≫ (Spec (.of k) ↘ Spec (.of k))).geometricGaloisFrobenius.asIso.hom :=
      MorphismProperty.of_isPullback hg.flip (inferInstance : WeaklyEtale (σₛ).hom)
    (inversePush (ℓ := ℓ) σₛ).hom.app ((R₀).obj K.obj) ≫
      compactificationInverseFrobeniusComponent Λ C h K.obj =
      (purityFieldCompactificationAmbientExchange ℓ f₀ f₀ c₀ c₀ hi hg).hom.app K.obj ≫
        (R₀).map ((inversePush (ℓ := ℓ) σₓ).hom.app K.obj) := by
  intro C h hi hg
  let z := (C.g ≫ (Spec (.of k) ↘ Spec (.of k))).geometricGaloisFrobenius.asIso
  have : @WeaklyEtale (c₀).Z (c₀).Z z.hom := MorphismProperty.of_isPullback hg.flip
    (inferInstance : WeaklyEtale (σₛ).hom)
  have core := namedArithmeticExchange Λ C h K.obj
  dsimp only at core
  have H := fieldExchangeOfExact (κ := Ω) (U := Xbar) (V := S₀) (ℓ := ℓ)
    f₀ c₀ σₓ σₛ z.hom hi hg K.obj (compactificationInverseFrobeniusComponent Λ C h K.obj)
    (by scheme_component_exact core using core)
  scheme_component_exact H using core

private theorem nativeComparison_component (K : Dᵇc((Xbar).left)⟦Λ⟧) :
    (changeCompactification (k := k) (ℓ := ℓ) (X := X)).hom.app K =
      (ambientCompactificationComparison ℓ (f := f₀) (compactificationOverField f₀) c₀ K).hom := by
  let a := compactificationOverField f₀
  let v := ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (f := f₀) a c₀).hom.app K).hom
  let w := (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f₀) c₀).hom.app K
  have ha := congrArg Iso.inv (compactificationCompatibility_component ℓ (f := f₀) a K)
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f₀) a).inv.app K = 𝟙 _ at ha
  exact ((congrArg (· ≫ v ≫ w) ha).trans (Category.id_comp _)).symm

private theorem pasteNative {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (s : F ≅ G) {P Q : A} {Z W V : B} (j : P ⟶ Q) (a : G.obj Q ⟶ V)
    (b : F.obj Q ⟶ Z) (e : F.obj P ⟶ W) (k : W ⟶ Z) (v : Z ⟶ V)
    (hb : s.hom.app Q ≫ a = b ≫ v) (hc : F.map j ≫ b = e ≫ k) :
    G.map j ≫ a = s.inv.app P ≫ e ≫ k ≫ v := by
  apply (cancel_epi (s.hom.app P)).mp
  rw [← Category.assoc, ← s.hom.naturality, Category.assoc, hb, ← Category.assoc,
    hc, Category.assoc, s.hom_inv_id_app_assoc]

private theorem nativeChosenComparison (K : Dᵇc((Xbar).left)⟦Λ⟧)
    (sq : IsPullback (σₓ).hom (f₀).left (f₀).left (σₛ).hom)
    (r : (c₀).Z ⟶ (c₀).Z) [WeaklyEtale r]
    (hi : IsPullback (c₀).i (σₓ).hom r (c₀).i) (hg : IsPullback r (c₀).g (c₀).g (σₛ).hom) :
    (CondensedRing.upperStar Λ (σₛ).hom).leftDerivedFunctor.map
        ((changeCompactification (k := k) (ℓ := ℓ) (X := X)).hom.app K) ≫
      (purityFieldCompactificationAmbientExchange ℓ f₀ f₀ c₀ c₀ hi hg).hom.app K.obj =
      ((purityFieldLowerShriekBaseChange ℓ f₀ f₀ sq).hom.app K).hom ≫
        (changeCompactification (k := k) (ℓ := ℓ) (X := X)).hom.app ((Fₓ).obj K) := by
  let σ := (specGeometricFrobenius k).asIso
  have overFrob {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) :
      a.geometricGaloisFrobenius.asIso.hom ≫ a.geometricFiberToAlgebraicClosure ≫ σ.inv =
        a.geometricFiberToAlgebraicClosure := by
    rw [← Category.assoc, a.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
      Category.assoc, σ.hom_inv_id, Category.comp_id]
  have H := chosenComparisonViaComponents (κ := Ω) (U := Xbar) (V := S₀) f₀ σ.symm (σₓ).hom (σₛ).hom
    (overFrob aX) (overFrob (Spec (.of k) ↘ Spec (.of k))) sq c₀ r hi hg
    (changeCompactification (k := k) (ℓ := ℓ) (X := X))
    (fun L ↦ by
      have cmp := nativeComparison_component L
      scheme_component_exact cmp using cmp) K
  scheme_component_exact H using H

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
/-- On the native structure map, changing compactification identifies the chosen shriek base
change with the two arithmetic inverse-pushforward exchanges, before inserting any Weil datum.

Source: the open and proper mate formulas in `SmoothPurityFieldCompactificationExchange`,
`CondensedModelWeilDerived`, and the normalized semilinear compactification comparison.
Give the middle scheme of the arithmetic geometric fibre the Frobenius of its structure
map. Its open and proper squares are Cartesian since all three Frobenius maps are invertible.
Compare the Nagata compactification and its pullback with this Cartesian pair using
`semilinearCompactificationExchange_normalized`. The transition on the output gives
the source change of compactification; the transition on the pulled-back coefficient
gives the target change. In the proper square take the right adjoint mate of the pullback
square. After conjugating endpoint pullbacks to inverse pushforward, its transpose is the
pushforward composition isomorphism for the inverse Frobenius square. In the open square
apply the same identification to restriction and take its left mate for extension by zero.
Derive the proper mate on the right and the exact open mate termwise. Composing the two
squares cancels the inverse-pushforward identification on the middle scheme and gives
the stated component. -/
theorem changeCompactification_frobenius (K : Dᵇc((Xbar).left)⟦Λ⟧) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let h := comp_over aX (Spec (.of k))
    let sq := IsPullback.of_horiz_isIso (Scheme.Hom.commSq_geometricGaloisFrobenius aX h)
    let E := purityFieldLowerShriekBaseChange ℓ f₀ f₀ sq
    let J := changeCompactification (k := k) (ℓ := ℓ) (X := X)
    (CondensedRing.lowerStar Λ (σₛ).inv).mapDerivedCategory.map (J.hom.app K) ≫
        compactificationInverseFrobeniusComponent Λ C h K.obj =
      (inversePush (ℓ := ℓ) σₛ).inv.app ((H₀).obj K).obj ≫ (E.hom.app K).hom ≫
        J.hom.app ((Fₓ).obj K) ≫ (R₀).map ((inversePush (ℓ := ℓ) σₓ).hom.app K.obj) := by
  intro C h sq E J
  let r := (C.g ≫ (Spec (.of k) ↘ Spec (.of k))).geometricGaloisFrobenius.asIso.hom
  let hi := (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap C.i (C.i_comp_g_comp h)).flip
  let hg := Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap C.g
    (rfl : C.g ≫ (Spec (.of k) ↘ Spec (.of k)) = _)
  have : @WeaklyEtale (c₀).Z (c₀).Z r := MorphismProperty.of_isPullback hg.flip
    (inferInstance : WeaklyEtale (σₛ).hom)
  let B := (purityFieldCompactificationAmbientExchange ℓ f₀ f₀ c₀ c₀ hi hg).hom.app K.obj
  have square := nativeChosenComparison K sq r hi hg
  let s := inversePush (ℓ := ℓ) σₛ
  let u := compactificationInverseFrobeniusComponent Λ C h K.obj
  let v := (R₀).map ((inversePush (ℓ := ℓ) σₓ).hom.app K.obj)
  have ambient := arithmeticAmbient K
  dsimp only at ambient
  let P := ((H₀).obj K).obj
  let Q := (R₀).obj K.obj
  let W := ((H₀).obj ((Fₓ).obj K)).obj
  let Z := (R₀).obj ((Fₓ).obj K).obj
  let V := (R₀).obj ((CondensedRing.lowerStar Λ (σₓ).inv).mapDerivedCategory.obj K.obj)
  have step := pasteNative (P := P) (Q := Q) (W := W) (Z := Z) (V := V)
    s (J.hom.app K) u B (E.hom.app K).hom (J.hom.app ((Fₓ).obj K)) v
    (by scheme_component_exact ambient using square) (by scheme_component_exact square using square)
  exact_by_kernel step

private theorem pasteCoefficient {C : Type*} [Category* C] {A B D E F G H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (w : D ⟶ I)
    (e : A ⟶ E) (p : E ⟶ F) (j : F ⟶ G) (r : G ⟶ D)
    (q : F ⟶ H) (z : H ⟶ I) (v : G ⟶ I)
    (square : a ≫ b = e ≫ p ≫ j ≫ r) (hv : r ≫ w = v) (nat : q ≫ z = j ≫ v) :
    a ≫ b ≫ w = (e ≫ p ≫ q) ≫ z := by
  rw [reassoc_of% square]
  simp only [Category.assoc, hv, nat]

/-- Evaluate the compactification exchange on a coefficient descent map. The naturality
of change of compactification moves the map across the comparison on the source. -/
theorem changeCompactification_equivariance (K : Dᵇc((Xbar).left)⟦Λ⟧)
    (v : (Fₓ).obj K ⟶ K)
    (w : (CondensedRing.lowerStar Λ (σₓ).inv).mapDerivedCategory.obj K.obj ⟶ K.obj)
    (hv : (inversePush (ℓ := ℓ) σₓ).hom.app K.obj ≫ w = v.hom) :
    let C := WeilComplex.structureMorphismCompactification (k₀ := k) X
    let h := comp_over aX (Spec (.of k))
    let sq := IsPullback.of_horiz_isIso (Scheme.Hom.commSq_geometricGaloisFrobenius aX h)
    let E := purityFieldLowerShriekBaseChange ℓ f₀ f₀ sq
    let J := changeCompactification (k := k) (ℓ := ℓ) (X := X)
    IsWeilEquivariant (CondensedRing.lowerStar Λ (σₛ).inv).mapDerivedCategory
      ((inversePush (ℓ := ℓ) σₛ).inv.app _ ≫ (E.hom.app K ≫ (H₀).map v).hom)
      (compactificationInverseFrobeniusComponent Λ C h K.obj ≫ (R₀).map w) (J.hom.app K) := by
  intro C h sq E J
  let S := (CondensedRing.lowerStar Λ (σₛ).inv).mapDerivedCategory
  let r := (inversePush (ℓ := ℓ) σₓ).hom.app K.obj
  have mapped : (R₀).map r ≫ (R₀).map w = (R₀).map v.hom :=
    ((R₀).map_comp r w).symm.trans (congrArg (R₀).map hv)
  have square := changeCompactification_frobenius K
  dsimp only at square
  refine pasteCoefficient (S.map (J.hom.app K)) (compactificationInverseFrobeniusComponent Λ C h K.obj)
    ((R₀).map w) ((inversePush (ℓ := ℓ) σₛ).inv.app _) (E.hom.app K).hom
    (J.hom.app ((Fₓ).obj K)) ((R₀).map r) ((H₀).map v).hom (J.hom.app K)
    ((R₀).map v.hom) ?_ mapped (J.hom.naturality v)
  scheme_component_exact square using hv

end NativePointShriek
end WeilII
