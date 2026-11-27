module

import WeilConjectures.Tactic.TransportExact

public import WeilII.AlgebraicGeometry.CondensedWeilPullAction
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-! # Geometric Frobenius on the pullback of a condensed Weil sheaf -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

universe u


variable {ℓ : ℕ} [Fact ℓ.Prime]
set_option quotPrecheck false



local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "V" => adicUpperStar ℓ
local notation "E" X => (adicSheafEquivCondensedMod ℓ X).functor
local notation "ξ" f => (adicUpperStarCompCondensedModIso ℓ f).inv

private lemma pasteComparison {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {A B I K : C} {X Y P Q : D} (a : A ≅ I) (b : B ≅ K) (w : A ≅ B)
    (c : X ≅ P) (d : Y ≅ Q) (v : X ≅ Y) (x : X ⟶ J.obj A) (y : Y ⟶ J.obj B)
    {P' Q' : D} (p : P ⟶ P') (p' : P' ⟶ J.obj I) (q : Q ⟶ Q') (q' : Q' ⟶ J.obj K)
    (hp : x = c.hom ≫ p ≫ p' ≫ J.map a.inv)
    (hq : y = d.hom ≫ q ≫ q' ≫ J.map b.inv)
    (hw : x ≫ J.map w.hom = v.hom ≫ y) :
    p ≫ p' ≫ J.map (a.inv ≫ w.hom ≫ b.hom) =
      (c.symm ≪≫ v ≪≫ d).hom ≫ q ≫ q' := by
  apply (cancel_epi c.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.map_comp]
  rw [← reassoc_of% hp, reassoc_of% hw, hq]
  simp only [Category.assoc, ← J.map_comp, Iso.inv_hom_id, J.map_id, Category.comp_id]

private lemma comparePaths {I N C D : Type*}
    [Category* I] [Category* N] [Category* C] [Category* D] (H : I ⥤ N) (J : C ⥤ D)
    {F G K L : I ⥤ C} {F' G' K' L' : N ⥤ D}
    (a : F ≅ K) (b : G ≅ L) (w : F ≅ G) (c : F' ≅ K') (d : G' ≅ L') (v : F' ≅ G')
    (x : H ⋙ F' ⟶ F ⋙ J) (y : H ⋙ G' ⟶ G ⋙ J) (M : I)
    {T₁ T₂ : D} (p : K'.obj (H.obj M) ⟶ T₁) (q : T₁ ⟶ J.obj (K.obj M))
    (p' : L'.obj (H.obj M) ⟶ T₂) (q' : T₂ ⟶ J.obj (L.obj M))
    (h : x.app M = c.hom.app (H.obj M) ≫ p ≫ q ≫ J.map (a.inv.app M))
    (h' : y.app M = d.hom.app (H.obj M) ≫ p' ≫ q' ≫ J.map (b.inv.app M))
    (hw : x.app M ≫ J.map (w.hom.app M) = v.hom.app (H.obj M) ≫ y.app M) :
    p ≫ q ≫ J.map (a.inv.app M ≫ w.hom.app M ≫ b.hom.app M) =
      ((c.app (H.obj M)).symm ≪≫ v.app (H.obj M) ≪≫ d.app (H.obj M)).hom ≫ p' ≫ q' :=
  pasteComparison J (a.app M) (b.app M) (w.app M) (c.app _) (d.app _) (v.app _)
    (x.app M) (y.app M) p q p' q' h h' hw

private lemma compComparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : AdicSheaf ℓ Z) :
    (ξ (f ≫ g)).app M =
      (CondensedRing.upperStarComp Λ f g).hom.app ((E Z).obj M) ≫
      (U f).map ((ξ g).app M) ≫ (ξ f).app ((V g).obj M) ≫
      (E X).map ((adicUpperStarComp ℓ f g).inv.app M) := by
  have h := NatTrans.congr_app (adicUpperStarCompCondensedModIso_comp_inv ℓ f g) M
  simpa only [TwoSquare.mk, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using h

/-- Changing coefficient model preserves the ordinary pullback square componentwise. -/
theorem adicCondensed_square {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {f : Y ⟶ W}
    {b : X ⟶ Z} {g : Z ⟶ W} (w : a ≫ f = b ≫ g) (M : AdicSheaf ℓ W) :
    (U a).map ((ξ f).app M) ≫ (ξ a).app ((V f).obj M) ≫
        (E X).map ((adicUpperStarComp ℓ a f).inv.app M ≫ (adicUpperStarCongr ℓ w).hom.app M ≫
          (adicUpperStarComp ℓ b g).hom.app M) =
      (CondensedRing.upperStarSquareIso Λ w ((E W).obj M)).hom ≫
        (U b).map ((ξ g).app M) ≫ (ξ b).app ((V g).obj M) := by
  have hc {d e : X ⟶ W} (h : d = e) :
      (ξ d).app M ≫ (E X).map ((adicUpperStarCongr ℓ h).hom.app M) =
        (CondensedRing.upperStarCongr Λ h).hom.app ((E W).obj M) ≫ (ξ e).app M := by
    subst e
    change (ξ d).app M ≫ (E X).map (𝟙 ((V d).obj M)) = 𝟙 _ ≫ (ξ d).app M
    rw [(E X).map_id]
    exact (Category.comp_id ((ξ d).app M)).trans (Category.id_comp _).symm
  unfold CondensedRing.upperStarSquareIso
  fo_apply (comparePaths (E W) (E X)
    (adicUpperStarComp ℓ a f) (adicUpperStarComp ℓ b g) (adicUpperStarCongr ℓ w)
    (CondensedRing.upperStarComp Λ a f) (CondensedRing.upperStarComp Λ b g)
    (CondensedRing.upperStarCongr Λ w) (ξ (a ≫ f)) (ξ (b ≫ g)) M
    ((U a).map ((ξ f).app M)) ((ξ a).app ((V f).obj M))
    ((U b).map ((ξ g).app M)) ((ξ b).app ((V g).obj M))
    ) using fo_late (compComparison a f M), fo_late (compComparison b g M), fo_late (hc w)

variable {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
local notation "γ" Z => (Z ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "fib" Z => (Z ↘ Spec (.of k)).geometricFiber

private lemma pullActionExchange {X Y : Scheme.{u}} (r : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
    (w : a.hom ≫ r = r ≫ b.hom) (M : AdicSheaf ℓ Y)
    (t : (adicLowerStar ℓ b.inv).obj M ≅ M) :
    (adicUpperStarIsoLowerStarInv ℓ a).hom.app ((V r).obj M) ≫ (upperStarStr ℓ w t).hom =
      ((adicUpperStarComp ℓ a.hom r).inv.app M ≫ (adicUpperStarCongr ℓ w).hom.app M ≫
        (adicUpperStarComp ℓ r b.hom).hom.app M) ≫
        (V r).map ((adicUpperStarIsoLowerStarInv ℓ b).hom.app M ≫ t.hom) := by
  simp only [upperStarStr, adicUpperStarExchangeIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]

private lemma nativePullAction_upperStar (r : X ⟶ Y) [r.IsOver (Spec (.of k))]
    (W : ProEtaleWeilSheaf k ℓ Y) :
    let f := Scheme.Hom.geometricFiberMap r (comp_over r (Spec (.of k)))
    let w := (Scheme.Hom.commSq_geometricGaloisFrobenius r (comp_over r (Spec (.of k)))).w
    nativePullAction ((ProEtaleWeilSheaf.upperStar k ℓ r).obj W) =
      ((adicUpperStarComp ℓ (γ X).hom f).inv.app W.carrier ≫
        (adicUpperStarCongr ℓ w).hom.app W.carrier ≫
        (adicUpperStarComp ℓ f (γ Y).hom).hom.app W.carrier) ≫
        (V f).map (nativePullAction W) := by
  dsimp only
  unfold nativePullAction
  rw [ProEtaleWeilSheaf.upperStar_obj_str_hom]
  transport_exact pullActionExchange (Scheme.Hom.geometricFiberMap r (comp_over r _)) (γ X) (γ Y)
    (Scheme.Hom.commSq_geometricGaloisFrobenius r (comp_over r _)).w W.carrier W.str

private lemma pasteActions {C D I : Type*} [Category* C] [Category* D] [Category* I]
    (J : C ⥤ D) (P : I ⥤ D) {A B T : C} {A' B' T' : I} {S S' : D}
    (x : S ⟶ S') (a : S' ⟶ J.obj A) (w : S ⟶ P.obj A') (b : A' ⟶ B')
    (m : B' ⟶ T') (q : A ⟶ B) (r : B ⟶ T) (c : P.obj B' ⟶ J.obj B)
    (t : P.obj T' ⟶ J.obj T) (v : S' ⟶ J.obj T) (v' : A' ⟶ T') (z : A ⟶ T)
    (hs : x ≫ a ≫ J.map q = w ≫ P.map b ≫ c) (hn : P.map m ≫ t = c ≫ J.map r)
    (hv : v = a ≫ J.map z) (hz : z = q ≫ r) (hv' : v' = b ≫ m) :
    x ≫ v = w ≫ P.map v' ≫ t := by
  rw [hv, hz, hv', J.map_comp, P.map_comp, Category.assoc, hn, reassoc_of% hs]

local notation "fiberMap" r => Scheme.Hom.geometricFiberMap r (comp_over r (Spec (.of k)))
local notation "fiberSquare" r =>
  (Scheme.Hom.commSq_geometricGaloisFrobenius r (comp_over r (Spec (.of k)))).w

/-- The inverse pullback comparison of the coefficient equivalence intertwines both ordinary
Weil structures across the Frobenius square of a map of geometric fibres. -/
theorem condensedPullbackWeilSquare (r : X ⟶ Y) [r.IsOver (Spec (.of k))]
    (W : ProEtaleWeilSheaf k ℓ Y) :
    let f := Scheme.Hom.geometricFiberMap r (comp_over r (Spec (.of k)))
    let w : (γ X).hom ≫ f = f ≫ (γ Y).hom := (Scheme.Hom.commSq_geometricGaloisFrobenius r (comp_over r (Spec (.of k)))).w
    (U (γ X).hom).map (X := (U f).obj ((E (fib Y)).obj W.carrier))
        (Y := ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj
          ((ProEtaleWeilSheaf.upperStar k ℓ r).obj W)).carrier) ((ξ f).app W.carrier) ≫
        ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj
          ((ProEtaleWeilSheaf.upperStar k ℓ r).obj W)).str.hom =
      (CondensedRing.upperStarSquareIso Λ (a := (γ X).hom) (b := f) (f := f) (g := (γ Y).hom)
        w ((E (fib Y)).obj W.carrier)).hom ≫
        (U f).map (X := (U (γ Y).hom).obj ((E (fib Y)).obj W.carrier))
          (Y := (E (fib Y)).obj W.carrier)
          (((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ Y).obj W).str.hom) ≫
        (ξ f).app W.carrier := by
  dsimp only
  have h := pasteActions (E (fib X)) (U (fiberMap r))
    ((U (γ X).hom).map ((ξ (fiberMap r)).app W.carrier)) ((ξ (γ X).hom).app ((V (fiberMap r)).obj W.carrier))
    (CondensedRing.upperStarSquareIso Λ (fiberSquare r) ((E (fib Y)).obj W.carrier)).hom
    ((ξ (γ Y).hom).app W.carrier) ((E (fib Y)).map (nativePullAction W))
    ((adicUpperStarComp ℓ (γ X).hom (fiberMap r)).inv.app W.carrier ≫
      (adicUpperStarCongr ℓ (fiberSquare r)).hom.app W.carrier ≫
      (adicUpperStarComp ℓ (fiberMap r) (γ Y).hom).hom.app W.carrier)
    ((V (fiberMap r)).map (nativePullAction W)) ((ξ (fiberMap r)).app ((V (γ Y).hom).obj W.carrier))
    ((ξ (fiberMap r)).app W.carrier) _ _ _
    (adicCondensed_square (fiberSquare r) W.carrier) ((ξ (fiberMap r)).naturality (nativePullAction W))
    (changeFrobeniusModel ((ProEtaleWeilSheaf.upperStar k ℓ r).obj W))
    (nativePullAction_upperStar r W) (changeFrobeniusModel W)
  transport_exact h

end WeilII.ExternalProduct
