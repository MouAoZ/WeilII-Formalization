module

public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.WeilSheaf.BaseChangeField.Comparison
import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pullback of Weil sheaves after finite extension of constants

Zhang, *On an elementary proof of Weil II*, p. 2, uses finite extensions of the constant field.
Pullback compatibility on the fiber-product models applies to the coordinate projections in the
proof of Proposition 1.5 on pp. 3–4.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- Pulling back a lisse Weil sheaf commutes with the finite extension of constants used in
Zhang, *On an elementary proof of Weil II*, pp. 2–4.

Write X' and Y' for the fiber products over k. The two projections of the induced map fK are
the composite with f and the projection to Spec K. With the same identification of algebraic
closures on both sides, the resulting geometric maps form a commutative square with the fiber
isomorphisms θX and θY. Since the cardinality of K is that of k to the power [K : k], each θ
intertwines the new Frobenius with this power of the old Frobenius. Let TX and TY transport
all pro-étale Weil sheaves along these isomorphisms with the iterated structure.

The Weil direct-image comparison gives an isomorphism β from TY f_* to fK_* TX by taking
the inverse of `transportLowerStarIso`. Under the two pullback–pushforward adjunctions its
mate goes from fK^* TY to TX f^*. At H first apply fK^* TY to the unit at H, then apply
fK^* to β at f^* H, then use the counit at TX (f^* H). These are Weil morphisms.

Forgetting the Weil structures sends the unit and counit to their geometric counterparts
and β to the inverse of the direct-image comparison of the geometric square. Thus the
underlying composite is the mate of that inverse at the underlying sheaf of H. Direct image
along each θ is an equivalence, with inverse given by direct image along its inverse.
The inverse mate of the geometric direct-image isomorphism is therefore invertible.
Both ends are constructible since pullback and extension of constants preserve constructibility.
Fullness gives the same morphism between constructible Weil sheaves. Its underlying morphism
is invertible, so it is a Weil isomorphism. Taking its inverse gives the stated direction. -/
public theorem weilSheaf_baseChangeField_upperStar
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] (H : WeilSheaf k ℓ Y) (_hH : H.IsLisse) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK : X.baseChangeField k K ⟶ Y.baseChangeField k K :=
      pullback.map (X ↘ Spec (CommRingCat.of k)) g (Y ↘ Spec (CommRingCat.of k)) g
        f (𝟙 _) (𝟙 _) (by simp) (by simp)
    letI : fK.IsOver (Spec (CommRingCat.of K)) :=
      ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩
    Nonempty ((WeilSheaf.baseChangeField K).obj ((WeilSheaf.upperStar f).obj H) ≅
      (WeilSheaf.upperStar fK).obj ((WeilSheaf.baseChangeField K).obj H)) := by
  intro g fK
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  let : fK.IsOver (Spec (CommRingCat.of K)) :=
    ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩
  let sqX := WeilSheaf.isPullback_baseChangeField (k₀ := k) X K
  let sqY := WeilSheaf.isPullback_baseChangeField (k₀ := k) Y K
  let θX := Scheme.Hom.geometricFiberBaseChangeIso sqX
  let θY := Scheme.Hom.geometricFiberBaseChangeIso sqY
  let d := Module.finrank k K
  have hX := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    sqX d Module.natCard_eq_pow_finrank
  have hY := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    sqY d Module.natCard_eq_pow_finrank
  let fbar := Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k)))
  let fKbar := Scheme.Hom.geometricFiberMap fK (comp_over fK (Spec (CommRingCat.of K)))
  have hsq : θX.hom ≫ fKbar = fbar ≫ θY.hom :=
    Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricFiberMap sqX sqY
      (comp_over f (Spec (CommRingCat.of k))) (comp_over fK (Spec (CommRingCat.of K)))
      (pullback.lift_fst _ _ _)

  -- Form the mate in the category of all pro-étale Weil sheaves.
  let TX := ProEtaleWeilSheaf.transport (Y := X) (Y' := X.baseChangeField k K) (l := ℓ) θX d hX
  let TY := ProEtaleWeilSheaf.transport (Y := Y) (Y' := Y.baseChangeField k K) (l := ℓ) θY d hY
  let F := ProEtaleWeilSheaf.upperStar k ℓ f
  let FK := ProEtaleWeilSheaf.upperStar K ℓ fK
  let R := ProEtaleWeilSheaf.lowerStar k ℓ f
  let RK := ProEtaleWeilSheaf.lowerStar K ℓ fK
  let adj : F ⊣ R := ProEtaleWeilSheaf.upperStarLowerStarAdjunction k ℓ f
  let adjK : FK ⊣ RK := ProEtaleWeilSheaf.upperStarLowerStarAdjunction K ℓ fK
  let σ : TX ⋙ RK ≅ R ⋙ TY :=
    ProEtaleWeilSheaf.transportLowerStarIso (l := ℓ) θX d hX θY hY f fK hsq
  let unit (M : ProEtaleWeilSheaf k ℓ Y) : M ⟶ R.obj (F.obj M) := adj.unit.app M
  let counit (M : ProEtaleWeilSheaf K ℓ (X.baseChangeField k K)) : FK.obj (RK.obj M) ⟶ M :=
    adjK.counit.app M
  let exchange (M : ProEtaleWeilSheaf k ℓ X) : TY.obj (R.obj M) ⟶ RK.obj (TX.obj M) :=
    σ.inv.app M
  let η := FK.map (TY.map (unit H.obj))
  let b := FK.map (exchange (F.obj H.obj))
  let ε := counit (TX.obj (F.obj H.obj))
  let m : FK.obj (TY.obj H.obj) ⟶ TX.obj (F.obj H.obj) := η ≫ b ≫ ε

  -- Its underlying map is the inverse mate of the geometric direct-image square.
  let s := ProEtale.adicLowerStarSquareIso ℓ hsq
  let a := ProEtale.adicUpperStarLowerStarAdjunction ℓ fbar
  let aK := ProEtale.adicUpperStarLowerStarAdjunction ℓ fKbar
  let γgeom := (mateEquiv a aK).symm s.inv
  have : IsIso γgeom := isIso_inverseMate_of_equivalences a aK s.symm
  have hm : m.hom.f = γgeom.app H.carrier :=
    (mateEquiv_symm_natTrans_app a aK s.inv H.carrier).symm
  have : IsIso m.hom.f :=
    (congrArg IsIso hm).mpr (NatIso.isIso_app_of_isIso γgeom H.carrier)
  have : IsIso ((Endofunctor.IsoAlgebra.forget _).map m) := ‹IsIso m.hom.f›
  have : IsIso m := isIso_of_reflects_iso m (Endofunctor.IsoAlgebra.forget _)

  -- Identify both endpoints in the constructible full subcategory.
  let extX := WeilSheaf.baseChangeField (k₀ := k) (l := ℓ) (X := X) K
  let extY := WeilSheaf.baseChangeField (k₀ := k) (l := ℓ) (X := Y) K
  let L := extX.obj ((WeilSheaf.upperStar f).obj H)
  let B := (WeilSheaf.upperStar fK).obj (extY.obj H)
  have hx (M : WeilSheaf k ℓ X) : (extX.obj M).obj = TX.obj M.obj := rfl
  have hy (M : WeilSheaf k ℓ Y) : (extY.obj M).obj = TY.obj M.obj := rfl
  have hf (M : WeilSheaf k ℓ Y) : ((WeilSheaf.upperStar f).obj M).obj = F.obj M.obj := rfl
  have hfK (M : WeilSheaf K ℓ (Y.baseChangeField k K)) :
      ((WeilSheaf.upperStar fK).obj M).obj = FK.obj M.obj := rfl
  let left : L.obj ≅ TX.obj (F.obj H.obj) :=
    eqToIso (hx ((WeilSheaf.upperStar f).obj H)) ≪≫ TX.mapIso (eqToIso (hf H))
  let right : B.obj ≅ FK.obj (TY.obj H.obj) :=
    eqToIso (hfK (extY.obj H)) ≪≫ FK.mapIso (eqToIso (hy H))
  let e : TX.obj (F.obj H.obj) ≅ FK.obj (TY.obj H.obj) := (asIso m).symm
  let lift {U V : WeilSheaf K ℓ (X.baseChangeField k K)} (i : U.obj ≅ V.obj) : U ≅ V :=
    ObjectProperty.isoMk _ i
  let result : L ≅ B := lift (left ≪≫ e ≪≫ right.symm)
  exact Nonempty.intro (α := L ≅ B) result

end WeilII
