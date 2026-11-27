module

import WeilConjectures.Tactic.FirstOrderApply
import WeilII.AlgebraicGeometry.UnderlyingPullbackSquareOfMap
import WeilII.AlgebraicGeometry.WeilPullbackSingleChart
import Mathlib.Util.TermReduce
import WeilII.AlgebraicGeometry.FrobeniusTensorChartPasting
import WeilII.AlgebraicGeometry.UnderlyingFrobeniusTensorAction
public import WeilII.AlgebraicGeometry.CompactSupportShiftedUnit
public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.WeilSheaf.TensorObjPairing
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilII.AlgebraicGeometry.NativeSingleFrobeniusChart
import WeilII.AlgebraicGeometry.NativeLisseTensorComparison
public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
import WeilII.AlgebraicGeometry.NormalizedWeilSingleEvaluation
import WeilII.AlgebraicGeometry.WeilSingleForgetComparison

/-!
# The geometric condensed carrier of an external tensor product of lisse Weil sheaves

Zhang, p. 2, uses the Frobenius-equivariant external tensor product in the compact-support
Künneth formula. The native coefficient object is the internal Hom in
`WeilSheaf/Tensor.lean`. Its local evaluation pairing is `Mod.toIhomDual`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

open CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

namespace ExternalProduct

variable {X P : Scheme.{u}} [X.Over (Spec (.of k))] [P.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (P ↘ Spec (.of k))] [LocallyOfFiniteType (P ↘ Spec (.of k))]
  [QuasiCompact (P ↘ Spec (.of k))]

/-- The degree-zero geometric carrier comparison, obtained from
`WeilComplex.condensedCarrierIso` and the exact functor comparisons with the single embedding. -/
def carrierSingle (L : WeilSheaf k ℓ X) :
    (carrier.obj L).obj ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor.obj L.obj.carrier) :=
  let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
  let V := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ X)
  WeilComplex.condensedCarrierIso (WeilSheaf.toComplex.obj L).obj ≪≫
    E.mapDerivedCategory.mapIso ((V.mapDerivedCategorySingleFunctor 0).app L.obj) ≪≫
    (E.mapDerivedCategorySingleFunctor 0).app L.obj.carrier

/-- The pulled-back geometric carrier as a single complex. The last comparison is the inverse
of `adicUpperStarCompCondensedModIso` at the underlying native sheaf. -/
def pullCarrierSingle (f : P ⟶ X) [f.IsOver (Spec (.of k))] (L : WeilSheaf k ℓ X) :
    (pull (ℓ := ℓ) (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k))))).obj
        (carrier.obj L).obj ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((adicSheafEquivCondensedMod ℓ (P ↘ Spec (.of k)).geometricFiber).functor.obj
        (((WeilSheaf.upperStar f).obj L).obj.carrier)) :=
  let f' := Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k)))
  let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
  (pull (ℓ := ℓ) f').mapIso (carrierSingle L) ≪≫
    ((CondensedRing.upperStar Λ f').singleFunctorCompLeftDerivedFunctorIso).app (E.obj L.obj.carrier) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (((adicUpperStarCompCondensedModIso ℓ f').app L.obj.carrier).symm)

/-- Naturality transports the derived Weil structure through a change of presentation.
The final structure map is evaluated after applying the exact forgetful functor. -/
private theorem carrierChartSquare {C D : Type*} [Category* C] [Category* D]
    {H U R : C ⥤ C} {V : D ⥤ C} (d : H ⟶ U) (t : U ⟶ R) (ρ : V ⋙ R ⟶ V)
    {A B : D} {Z B₀ : C} (w : A ⟶ B) (b : V.obj B ⟶ Z) (a : V.obj A ⟶ Z)
    (ha : a = V.map w ≫ b) (r : R.obj Z ⟶ B₀) (z : B₀ ⟶ Z) (h : ρ.app B ≫ b = R.map b ≫ r ≫ z) :
    (d.app (V.obj A) ≫ t.app (V.obj A) ≫ ρ.app A) ≫ a =
      H.map a ≫ ((d.app Z ≫ t.app Z) ≫ r) ≫ z := by
  rw [ha, H.map_comp]
  have hn := ρ.naturality w
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, h, ← t.naturality_assoc, ← t.naturality_assoc,
    ← d.naturality_assoc, ← d.naturality_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- In the geometric single chart of a Weil sheaf, its carrier Frobenius becomes
the ordinary condensed Weil structure placed in degree zero. -/
theorem carrierSingle_frobenius (I : WeilSheaf k ℓ X) :
    (carrierFrobenius I).hom.hom ≫ (ExternalProduct.carrierSingle I).hom =
      (pull (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom).map
        (ExternalProduct.carrierSingle I).hom ≫ ExternalProduct.singleFrobenius I.obj := by
  let γ := (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
  let U := CondensedRing.upperStar Λ γ.hom
  let R := CondensedRing.lowerStar Λ γ.inv
  let T := ProEtaleWeilSheaf.toCondensed k ℓ X
  let V' := IsoAlgebra.forget R
  let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
  let W := T.obj I.obj
  let w := (T.mapDerivedCategorySingleFunctor 0).hom.app I.obj
  let b := (V'.mapDerivedCategorySingleFunctor 0).hom.app W
  have hb : (ExternalProduct.carrierSingle I).hom = V'.mapDerivedCategory.map w ≫ b :=
    ExternalProduct.forgetComparison_single
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X) I.obj
  let t := CondensedRing.upperStarIsoLowerStarInv Λ γ
  let d := U.leftDerivedFunctorIsoMapDerivedCategory
  let dt := Functor.mapDerivedCategoryNatIso t
  have hs := IsoAlgebra.derivedStrIso_hom_app_singleFunctor_obj R W
  have key := carrierChartSquare
    (H := U.leftDerivedFunctor) (U := U.mapDerivedCategory) (R := R.mapDerivedCategory)
    (V := V'.mapDerivedCategory) d.hom dt.hom (IsoAlgebra.derivedStrIso R).hom w b
    (ExternalProduct.carrierSingle I).hom hb
    ((R.mapDerivedCategorySingleFunctor 0).hom.app W.carrier) (S.map W.str.hom) hs
  exact key

/-- Postcompose with the target chart to test equivariance of a normalized map. -/
private theorem equivarianceOfNormalizedMap {C : Type*} [Category* C] (H : C ⥤ C)
    {V I W O : C} (a : V ⟶ I) (q : I ⟶ O) (b : W ≅ O) (z : V ⟶ W)
    (g : H.obj V ⟶ V) (w : H.obj W ⟶ W) (i : H.obj I ⟶ I) (o : H.obj O ⟶ O)
    (hn : z ≫ b.hom = a ≫ q) (ha : H.map a ≫ i = g ≫ a)
    (hb : w ≫ b.hom = H.map b.hom ≫ o) (hj : H.map q ≫ o = i ≫ q) :
    H.map z ≫ w = g ≫ z := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, hb]
  rw [← H.map_comp_assoc, hn, H.map_comp, Category.assoc, hj, reassoc_of% ha]

/-- A bounded coefficient map with the normalized degree-zero evaluation commutes
with Frobenius whenever its source chart intertwines the specified source action.
The first sheaf supplies the lisse evaluation, and the right factor is arbitrary. -/
theorem normalizedCarrierMap_of_source (F G : WeilSheaf k ℓ X) (hF : F.IsLisse)
    (j : (Mod.tensorLeft G.obj.carrier).obj F.obj.carrier ⟶ (F.tensorObj G hF).obj.carrier)
    (hj : Mod.tensorπ F.obj.carrier G.obj.carrier ≫ j.hom =
      Mod.toIhomDual F.obj.carrier G.obj.carrier) :
    let Q := boundedConstructible (condensedRingObj Λ (X ↘ Spec (.of k)).geometricFiber)
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let T := ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj
    let N := F.tensorObj G hF
    ∀ (V : Q.FullSubcategory) (a : V.obj ⟶ S.obj (E.obj T.carrier))
      (z : V ⟶ carrier.obj N) (g : H.obj V.obj ⟶ V.obj),
      z.hom ≫ (carrierSingle N).hom = a ≫ S.map (E.map j) →
      H.map a ≫ singleFrobenius T = g ≫ a →
      H.map z.hom ≫ (carrierFrobenius N).hom.hom = g ≫ z.hom := by
  intro Q H E S T N V a z g hn ha
  let b := carrierSingle N
  let q := S.map (E.map j)
  have hb := carrierSingle_frobenius N
  have he := normalizedEvaluation_frobenius F G hF j hj
  exact equivarianceOfNormalizedMap H a q b z.hom g (carrierFrobenius N).hom.hom
    (singleFrobenius T) (singleFrobenius N.obj) hn ha hb he

end ExternalProduct

section

/-- A bundled scheme over the field carries its given structure map. -/
local instance (Z : Over (Spec (.of k))) : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩

/-- A morphism in the slice commutes with the two chosen structure maps. -/
local instance {U V : Over (Spec (.of k))} (f : U ⟶ V) : f.left.IsOver (Spec (.of k)) :=
  ⟨Over.w f⟩

/-- Separatedness for the structure map of the underlying scheme. -/
local instance (Z : Over (Spec (.of k))) [IsSeparated Z.hom] :
    IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)

/-- Local finite type for the structure map of the underlying scheme. -/
local instance (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (Z.left ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType Z.hom)

/-- Quasi-compactness for the structure map of the underlying scheme. -/
local instance (Z : Over (Spec (.of k))) [QuasiCompact Z.hom] :
    QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)

variable {X Y P : Over (Spec (.of k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]

/-- Conjugating an isomorphism between two presentations lifts it to a full subcategory.
Postcomposition with the target presentation determines the lift. -/
private theorem liftComparison {C : Type*} [Category* C] {Q : ObjectProperty C}
    {V W : Q.FullSubcategory} {A B : C} (a : V.obj ≅ A) (v : A ≅ B) (b : W.obj ≅ B)
    {I : Type*} (map : I → (A ⟶ B)) (gen : I → Prop) (j : I)
    (hj : gen j) (hs : ∀ x, gen x → x = j) (hm : map j = v.hom) :
    let e : V ≅ W := Q.isoMk (a ≪≫ v ≪≫ b.symm)
    let norm := fun t : V ≅ W ↦ ∃ x, gen x ∧ t.hom.hom ≫ b.hom = a.hom ≫ map x
    norm e ∧ (∀ e', norm e' → e' = e) ∧ e.hom.hom ≫ b.hom = a.hom ≫ map j := by
  intro e norm
  have fac : e.hom.hom ≫ b.hom = a.hom ≫ map j := by
    change (a.hom ≫ v.hom ≫ b.inv) ≫ b.hom = _
    simp only [hm, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨⟨j, hj, fac⟩, ?_, fac⟩
  rintro e' ⟨x, hx, h⟩
  obtain rfl := hs x hx
  exact Iso.ext (ObjectProperty.hom_ext _ ((cancel_mono b.hom).1 (h.trans fac.symm)))

/-- The normalized isomorphism between the two single-complex presentations is unique. -/
private theorem existsUniqueNormalized
    (p : P ⟶ X) (s : P ⟶ Y)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let pStar := boundedConstructibleUpperStar Λ ℓ p'
    let sStar := boundedConstructibleUpperStar Λ ℓ s'
    let K := carrier.obj L
    let J := carrier.obj M
    let F := (WeilSheaf.upperStar p.left).obj L
    let G := (WeilSheaf.upperStar s.left).obj M
    let N := F.tensorObj G (hL.upperStar p.left)
    let A := F.obj.carrier
    let B := G.obj.carrier
    let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
    let flatTensor := (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso
      (E.obj B) 0
    let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
        (ExternalProduct.pullCarrierSingle s.left M) ≪≫
      flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
    let normalized := fun e : pStar.obj K ⊗ sStar.obj J ≅ carrier.obj N ↦
      ∃ j : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier,
        Mod.tensorπ A B ≫ j.hom = Mod.toIhomDual A B ∧
        e.hom.hom ≫ (ExternalProduct.carrierSingle N).hom = sourceSingle.hom ≫ S.map (E.map j)
    ∃ e, normalized e ∧ (∀ e', normalized e' → e' = e) := by
  let _ : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  let _ : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let _ := (monoidalCategory_boundedConstructible (ℓ := ℓ)
    (geometricFiberOver P)).toMonoidalCategoryStruct
  intro p' s' pStar sStar K J F G N A B E S flatTensor sourceSingle normalized
  have native := nativeLisseTensorComparison F G (hL.upperStar p.left)
  let t := native.choose
  have ht := native.choose_spec
  let U := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ P.left)
  let j : (Mod.tensorLeft B).obj A ≅ N.obj.carrier := U.mapIso t
  let V := pStar.obj K ⊗ sStar.obj J
  let W := carrier.obj N
  let I := S.obj (E.obj ((Mod.tensorLeft B).obj A))
  let O := S.obj (E.obj N.obj.carrier)
  let a : V.obj ≅ I := sourceSingle
  let b : W.obj ≅ O := ExternalProduct.carrierSingle N
  let v : I ≅ O := S.mapIso (E.mapIso j)
  let map (f : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier) : I ⟶ O := S.map (E.map f)
  let gen (f : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier) :=
    Mod.tensorπ A B ≫ f.hom = Mod.toIhomDual A B
  have onlyGen (f : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier) (hf : gen f) : f = j.hom :=
    Mod.tensorLeft_hom_ext B A (Mod.hom_ext _ _ (hf.trans ht.symm))
  have lifted := liftComparison (Q := boundedConstructible (condensedRingObj Λ P.hom.geometricFiber))
    (V := V) (W := W) (A := I) (B := O) a v b map gen j.hom ht onlyGen rfl
  let e : V ≅ W := ObjectProperty.isoMk _ (a ≪≫ v ≪≫ b.symm)
  exact ⟨e, lifted.1, lifted.2.1⟩

/-- The chart of the pullback of a degree-zero Weil sheaf intertwines geometric
Frobenius with the geometric pullback square. Source: the native
`adicUpperStarGeometricFiberMapCompFrobeniusIso` and
`adicUpperStarCompCondensedModIso_comp_inv`.

Proof. Expand the chart into pullback of the carrier chart, the comparison for an
exact pullback on singles, and the single of the inverse coefficient comparison.
Move the first map across the natural pullback square and apply
`carrierSingle_frobenius`. Evaluate each of the two derived composition isomorphisms
in the square on a single by `leftDerivedFunctorCompIso_hom_app_singleFunctor_obj`
and `leftDerivedFunctorNatIso_hom_app_singleFunctor_obj`. This leaves the square for
ordinary pullbacks. The native pullback Weil structure is the inverse-pushforward to
pullback comparison, followed by inverse composition, transport across the geometric
Frobenius square, forward composition and pullback of the input structure. Apply
`adicUpperStarCompCondensedModIso_inv_of_iso` to the endpoint comparisons,
`adicUpperStarCompCondensedModIso_comp_inv` to the two compositions, and
`adicUpperStarCompCondensedModIso_inv_congr` to the transport. Naturality on the
input Weil structure then identifies the two composites. -/
theorem ExternalProduct.pullCarrierSingle_frobenius (r : P ⟶ X) (I : WeilSheaf k ℓ X.left) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    let r' := geometricFiberOverMap r
    let R := boundedConstructibleUpperStar Λ ℓ r'
    let D := boundedConstructibleUpperStarOfMapSquareIso ℓ r' r'
      (Scheme.Hom.commSq_geometricGaloisFrobenius r.left (Over.w r)).w
    let a := (ExternalProduct.pullCarrierSingle r.left I).hom
    (pull P.hom.geometricGaloisFrobenius.asIso.hom).map a ≫
        ExternalProduct.singleFrobenius ((WeilSheaf.upperStar r.left).obj I).obj =
      (D.hom.app (carrier.obj I)).hom ≫ (R.map (carrierFrobenius I).hom).hom ≫ a := by
  have : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  have : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  dsimp only
  fo_apply (ExternalProduct.weilPullbackSingleIsoChart r.left I.obj (carrier.obj I).obj
    (ExternalProduct.carrierSingle I) (carrierFrobenius I).hom.hom
    (ExternalProduct.pullCarrierSingle r.left I)) using
    _, _, fo_late (ExternalProduct.pullCarrierSingle.eq_1 r.left I),
    fo_late (boundedConstructibleUpperStar_map_hom Λ ℓ (geometricFiberOverMap r) (carrierFrobenius I).hom),
    fo_late (underlyingPullbackSquareOfMap ℓ (geometricFiberOverMap r) (geometricFiberOverMap r)
      (Scheme.Hom.commSq_geometricGaloisFrobenius r.left (Over.w r)) (carrier.obj I)),
    fo_late (ExternalProduct.carrierSingle_frobenius I)

/-- The Frobenius action defined by the two projections takes each pulled-back generator
of the native relative tensor to the tensor of its two Weil images. Source: Zhang, p. 2,
`WeilSheaf/StalkUpperStar.lean`, `adicUpperStar_condensedRelativeTensor_square`, and
`leftDerivedUpperStarTensor_laxSquare`.

For a projection, expand `pullCarrierSingle` into pullback of the carrier chart, the exact
single comparison and the change of coefficient model. Move the carrier chart across the
pullback square by naturality and use `carrierSingle_frobenius`. On the resulting singles
the two derived composition comparisons are the ordinary composition comparisons. The
change-of-model comparisons preserve compositions, transports by equality, and the
identification of Frobenius pullback with inverse pushforward. Thus the remaining map on
each factor is its native pullback Weil structure. Tensor the two projection equalities.
Naturality of the oplax tensor comparison moves the two charts past that comparison.
Evaluate the tensor comparison on the two degree-zero representatives with
`leftDerivedUpperStarTensor_laxSquare`; the exact-pullback counits are isomorphisms, and
local freeness makes the left representatives K-flat before and after pullback. Cancelling
these comparisons gives the ordinary pullback tensor constraint in bidegree (0,0).
The ordinary change of relative tensor model commutes with this constraint by
`adicUpperStar_condensedRelativeTensor_square`. On the pulled-back quotient the two
resulting arrows have the value `(F.str.hom.hom ⊗ₘ G.str.hom.hom) ≫ Mod.tensorπ A B`
by `ProEtaleWeilSheaf.tensorπ_str`. This is the required generator equation. -/
theorem ExternalProduct.projectionFrobenius_on_tensorGenerators
    (p : P ⟶ X) (s : P ⟶ Y)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) :
    zeta%
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let pStar := boundedConstructibleUpperStar Λ ℓ p'
    let sStar := boundedConstructibleUpperStar Λ ℓ s'
    let K := carrier.obj L
    let J := carrier.obj M
    let F := (WeilSheaf.upperStar p.left).obj L
    let G := (WeilSheaf.upperStar s.left).obj M
    let A := F.obj.carrier
    let B := G.obj.carrier
    let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
    let flatTensor := (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso
      (E.obj B) 0
    let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
        (ExternalProduct.pullCarrierSingle s.left M) ≪≫
      flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
    let Fr := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
      (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
    let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
    let V := pStar.obj K ⊗ sStar.obj J
    let g : Fr.obj V ⟶ V := Functor.OplaxMonoidal.δ Fr (pStar.obj K) (sStar.obj J) ≫
      (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫
      (pStar.map (carrierFrobenius L).hom ⊗ₘ sStar.map (carrierFrobenius M).hom)
    ExternalProduct.ActsOnTensorGenerators F.obj G.obj sourceSingle g.hom := zeta% (by
  let : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  let : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
  let p' := geometricFiberOverMap p
  let s' := geometricFiberOverMap s
  let pStar := boundedConstructibleUpperStar Λ ℓ p'
  let sStar := boundedConstructibleUpperStar Λ ℓ s'
  let K := carrier.obj L
  let J := carrier.obj M
  let F := (WeilSheaf.upperStar p.left).obj L
  let G := (WeilSheaf.upperStar s.left).obj M
  let A := F.obj.carrier
  let B := G.obj.carrier
  let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
  let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
  let flatTensor := (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso
      (E.obj B) 0
  let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
        (ExternalProduct.pullCarrierSingle s.left M) ≪≫
      flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
  let Fr := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
      (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
  let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
  let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
  let V := pStar.obj K ⊗ sStar.obj J
  let g : Fr.obj V ⟶ V := Functor.OplaxMonoidal.δ Fr (pStar.obj K) (sStar.obj J) ≫
      (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫
      (pStar.map (carrierFrobenius L).hom ⊗ₘ sStar.map (carrierFrobenius M).hom)
  let U := pStar.obj K
  let W := sStar.obj J
  let d := Dp.hom.app K
  let e := Ds.hom.app J
  let c := pStar.map (carrierFrobenius L).hom
  let c' := sStar.map (carrierFrobenius M).hom
  have hg := ExternalProduct.boundedPullbackTensorAction_hom ℓ (geometricFiberOver P)
    P.hom.geometricGaloisFrobenius.asIso.hom U W _ _ d e c c'
  have hp := ExternalProduct.pullCarrierSingle_frobenius p L
  have hs := ExternalProduct.pullCarrierSingle_frobenius s M
  have pasted := ExternalProduct.generators_of_factor_charts F G (hL.upperStar p.left)
    (ExternalProduct.pullCarrierSingle p.left L)
    (ExternalProduct.pullCarrierSingle s.left M) d.hom e.hom c.hom c'.hom sourceSingle g.hom rfl hp hs hg
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let proof := (← Lean.Meta.getLocalDeclFromUserName `pasted).toExpr
    let normalize := fun e ↦ do
      Lean.Meta.withReducible <| Lean.Meta.whnf (← Lean.Meta.zetaReduce (← Lean.instantiateMVars e))
    let target ← normalize (← goal.getType)
    let given ← normalize (← Lean.Meta.inferType proof)
    unless target.consumeMData == given.consumeMData do
      throwError "the generator chart differs from the prescribed source chart"
    goal.assign proof)

set_option backward.isDefEq.respectTransparency.types false in
/-- A normalized single-complex comparison carries the tensor Frobenius on the pullbacks
to the Galois Frobenius on the tensor carrier. Source: the Weil pullback square in
`WeilSheaf/StalkUpperStar.lean`, the relative tensor square in
`Native/Projection/AdicSheafTensorSquare.lean`, and
`leftDerivedUpperStarTensor_laxSquare`.

Proof. By the normalized native tensor comparison, there is a Weil isomorphism t with
the prescribed value on pure tensors. The coefficient map in the normalization equals
its underlying map by extensionality on the relative tensor quotient. Thus the
degree-zero chart of e is the single of t. On the two input sheaves the Weil pullback
square moves geometric Frobenius past p and s. The model comparison for pullback is
the mate of the pushforward comparison, so composition of these squares respects change
of model. The ordinary relative tensor square identifies the two factor maps with the
native tensor structure, and t commutes with this structure. Embed the square in degree
zero. The first factor is locally free both before and after pullback, so its single is
K-flat in both places. In the derived pullback-tensor square on representatives cancel
the invertible localization comparisons and exact-pullback counits. The sole remaining
tensor term has bidegree (0,0) and is the ordinary square above. Conjugating by the
equivariant carrier charts gives the displayed equation. -/
theorem ExternalProduct.normalizedSingleTensor_frobenius
    (p : P ⟶ X) (s : P ⟶ Y)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let pStar := boundedConstructibleUpperStar Λ ℓ p'
    let sStar := boundedConstructibleUpperStar Λ ℓ s'
    let K := carrier.obj L
    let J := carrier.obj M
    let F := (WeilSheaf.upperStar p.left).obj L
    let G := (WeilSheaf.upperStar s.left).obj M
    let N := F.tensorObj G (hL.upperStar p.left)
    let A := F.obj.carrier
    let B := G.obj.carrier
    let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
    let flatTensor := (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso
      (E.obj B) 0
    let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
        (ExternalProduct.pullCarrierSingle s.left M) ≪≫
      flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
    let normalized := fun e : pStar.obj K ⊗ sStar.obj J ≅ carrier.obj N ↦
      ∃ j : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier,
        Mod.tensorπ A B ≫ j.hom = Mod.toIhomDual A B ∧
        e.hom.hom ≫ (ExternalProduct.carrierSingle N).hom = sourceSingle.hom ≫ S.map (E.map j)
    let Fr := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
      (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
    let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
    ∀ e, normalized e →
      Fr.map e.hom ≫ (carrierFrobenius N).hom =
        Functor.OplaxMonoidal.δ Fr (pStar.obj K) (sStar.obj J) ≫
          (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫
          (pStar.map (carrierFrobenius L).hom ⊗ₘ sStar.map (carrierFrobenius M).hom) ≫ e.hom := zeta% (by
  let _ : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  let _ : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let _ := (monoidalCategory_boundedConstructible (ℓ := ℓ)
    (geometricFiberOver P)).toMonoidalCategoryStruct
  intro p' s' pStar sStar K J F G N A B E S flatTensor sourceSingle normalized Fr Dp Ds e hn
  obtain ⟨j, hj, hn⟩ := hn
  let V := pStar.obj K ⊗ sStar.obj J
  let g : Fr.obj V ⟶ V :=
    Functor.OplaxMonoidal.δ Fr (pStar.obj K) (sStar.obj J) ≫
        (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫
        (pStar.map (carrierFrobenius L).hom ⊗ₘ sStar.map (carrierFrobenius M).hom)
  have transport := ExternalProduct.normalizedCarrierMap_of_source F G (hL.upperStar p.left) j hj
    V sourceSingle.hom e.hom g.hom hn
  suffices h : Fr.map e.hom ≫ (carrierFrobenius N).hom = g ≫ e.hom by
    exact h.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
  refine ObjectProperty.hom_ext _ (transport ?_)
  refine ExternalProduct.tensorSingleChart_of_generators F.obj G.obj sourceSingle g.hom ?_
  have hp := ExternalProduct.projectionFrobenius_on_tensorGenerators p s L M hL
  -- The proof term and the statement expand the same projection charts.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let proof := (← Lean.Meta.getLocalDeclFromUserName `hp).toExpr
    let normalize := fun e ↦ do
      Lean.Meta.withReducible <| Lean.Meta.whnf (← Lean.Meta.zetaReduce e)
    let target ← normalize (← goal.getType)
    let given ← normalize (← Lean.Meta.inferType proof)
    unless target.consumeMData == given.consumeMData do
      throwError "the Frobenius charts differ"
    goal.assign proof)

private theorem attachProperty {T : Sort*} {n f : T → Prop}
    (ex : ∃ x, n x ∧ ∀ y, n y → y = x) (hf : ∀ x, n x → f x) :
    ∃ x, n x ∧ (∀ y, n y → y = x) ∧ f x := by
  obtain ⟨x, hx, hu⟩ := ex
  exact ⟨x, hx, hu, hf x hx⟩

/-- The external tensor product of the two pulled-back condensed carriers has a unique
isomorphism to the carrier of the native tensor product normalized by evaluation on pure tensors.
This isomorphism intertwines geometric Galois Frobenius. Source: Zhang, p. 2, and
`WeilSheaf/TensorObjPairing.lean`, `Native/Projection/AdicSheafTensorSquare.lean`.

Proof. Write A and B for the two pulled-back native module sheaves. Evaluation sends
(v,w) to the map θ ↦ θ(v)w. This is additive and restriction-compatible in each variable,
and θ(cv)w = θ(v)(cw) = cθ(v)w, so it descends to a module map j from the relative
tensor to Hom(A∨,B). On a pro-étale trivialization of A with basis eᵢ and dual basis eⁱ,
send h to the sum of eᵢ ⊗ h(eⁱ). Applying evaluation to the sum at θ gives h(θ) by the
dual-basis expansion of θ. Applying the sum to the image of v ⊗ w gives v ⊗ w by the
basis expansion of v. Pure tensors generate locally and restriction commutes with internal Hom
on this cover, so the local inverses agree on overlaps and give a global inverse. This also
works for rank zero, where the sum is empty.

Pass to degree zero using the exact coefficient equivalence and exact pullbacks. The condensed
realization of A is locally free, hence its single complex is K-flat. Tensoring the two singles
therefore gives the single of the ordinary relative tensor. Composing the inverse condensed
relative tensor comparison with the image of j and the inverse target single comparison gives
the required isomorphism in the full bounded constructible subcategory. The quotient projection
determines j by its value on pure tensors, and full faithfulness of the single embedding gives
uniqueness in the derived category.

For Frobenius, commute pullback past each geometric projection using the pullback composition
square. The resulting structure maps are the structures on the two pulled-back Weil sheaves.
The coefficient comparison is the mate of the identity comparison on underlying pushforwards,
so these two composition squares are preserved under change of model. The relative tensor
comparison commutes with Frobenius pullback by `adicUpperStar_condensedRelativeTensor_square`.
After precomposition with the tensor projection, equivariance of j is exactly
`WeilSheaf.toIhomDual_str`, using pullback along Frobenius as inverse pushforward.
On single representatives `leftDerivedUpperStarTensor_laxSquare` identifies the derived
pullback tensor constraint with the degree-zero constraint: exact pullback makes the counits
invertible, and local freeness before and after pullback makes the localization tensor maps
invertible. Transport the resulting square to the three actual carriers via the equivariance
of the condensed forgetful comparison. -/
theorem weilLisseExternalProductCondensedComparison
    (p : P ⟶ X) (s : P ⟶ Y)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) (hM : M.IsLisse) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let pStar := boundedConstructibleUpperStar Λ ℓ p'
    let sStar := boundedConstructibleUpperStar Λ ℓ s'
    let K := carrier.obj L
    let J := carrier.obj M
    let F := (WeilSheaf.upperStar p.left).obj L
    let G := (WeilSheaf.upperStar s.left).obj M
    let N := F.tensorObj G (hL.upperStar p.left)
    let A := F.obj.carrier
    let B := G.obj.carrier
    let E := (adicSheafEquivCondensedMod ℓ P.hom.geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ P.hom.geometricFiber) 0
    let flatTensor := (IsAdicLisseSheaf.isLocallyFree (hL.upperStar p.left)).singleFunctorTensorObjIso
      (E.obj B) 0
    let sourceSingle := tensorIso (ExternalProduct.pullCarrierSingle p.left L)
        (ExternalProduct.pullCarrierSingle s.left M) ≪≫
      flatTensor ≪≫ S.mapIso (condensedRelativeTensorIso ℓ _ A B).symm
    let normalized := fun e : pStar.obj K ⊗ sStar.obj J ≅ carrier.obj N ↦
      ∃ j : (Mod.tensorLeft B).obj A ⟶ N.obj.carrier,
        Mod.tensorπ A B ≫ j.hom = Mod.toIhomDual A B ∧
        e.hom.hom ≫ (ExternalProduct.carrierSingle N).hom = sourceSingle.hom ≫ S.map (E.map j)
    let Fr := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
      (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
    let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
    ∃ e, normalized e ∧ (∀ e', normalized e' → e' = e) ∧
      Fr.map e.hom ≫ (carrierFrobenius N).hom =
        Functor.OplaxMonoidal.δ Fr (pStar.obj K) (sStar.obj J) ≫
          (Dp.hom.app K ⊗ₘ Ds.hom.app J) ≫
          (pStar.map (carrierFrobenius L).hom ⊗ₘ sStar.map (carrierFrobenius M).hom) ≫ e.hom := by
  exact attachProperty (existsUniqueNormalized p s L M hL)
    (ExternalProduct.normalizedSingleTensor_frobenius p s L M hL)

end

end WeilII
