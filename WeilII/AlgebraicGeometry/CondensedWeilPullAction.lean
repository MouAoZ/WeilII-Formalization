module

import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.Tactic.TransportExact

public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback

/-! # Changing the coefficient model of a Weil action -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilII.ExternalProduct

universe u


variable {ℓ : ℕ} [Fact ℓ.Prime]
set_option quotPrecheck false
set_option maxHeartbeats 100000


local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "V" => adicUpperStar ℓ
local notation "E" X => (adicSheafEquivCondensedMod ℓ X).functor
local notation "ξ" f => (adicUpperStarCompCondensedModIso ℓ f).inv

private lemma isoComparison {X Y : Scheme.{u}} (e : X ≅ Y) (M : AdicSheaf ℓ Y) :
    (ξ e.hom).app M ≫ (E X).map ((adicUpperStarIsoLowerStarInv ℓ e).hom.app M) =
      (CondensedRing.upperStarIsoLowerStarInv Λ e).hom.app ((E Y).obj M) ≫
      (adicLowerStarCompCondensedModIso ℓ e.inv).inv.app M := by
  have h := NatTrans.congr_app (adicUpperStarCompCondensedModIso_inv_of_iso ℓ e) M
  simp only [TwoSquare.mk, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(E X).map_id, Category.comp_id]

private lemma mappedAction {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {F L : C ⥤ C} {G R : D ⥤ D} (v : F ≅ L) (u : G ≅ R)
    (d : J ⋙ R ≅ L ⋙ J) (x : J ⋙ G ⟶ F ⋙ J) (W : IsoAlgebra L)
    (h : x.app W.carrier ≫ J.map (v.hom.app W.carrier) =
      u.hom.app (J.obj W.carrier) ≫ d.hom.app W.carrier) :
    ((IsoAlgebra.mapOfNatIso (Functor.isoWhiskerLeft J u ≪≫ d)).obj W).str.hom =
      x.app W.carrier ≫ J.map (v.hom.app W.carrier ≫ W.str.hom) := by
  change (u.hom.app _ ≫ d.hom.app _) ≫ J.map W.str.hom = _
  rw [← h, Category.assoc, ← J.map_comp]

private lemma actionOfIso {Z : Scheme.{u}} (e : Z ≅ Z) (W : IsoAlgebra (adicLowerStar ℓ e.inv)) :
    ((IsoAlgebra.mapOfNatIso (Functor.isoWhiskerLeft (E Z)
        (CondensedRing.upperStarIsoLowerStarInv Λ e) ≪≫
      (adicLowerStarCompCondensedModIso ℓ e.inv).symm)).obj W).str.hom =
      (ξ e.hom).app W.carrier ≫
      (E Z).map ((adicUpperStarIsoLowerStarInv ℓ e).hom.app W.carrier ≫ W.str.hom) := by
  cast_proofs mappedAction (E Z) (adicUpperStarIsoLowerStarInv ℓ e)
    (CondensedRing.upperStarIsoLowerStarInv Λ e) (adicLowerStarCompCondensedModIso ℓ e.inv).symm
    (ξ e.hom) W (isoComparison e W.carrier)

variable {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
local notation "γ" Z => (Z ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "fib" Z => (Z ↘ Spec (.of k)).geometricFiber

/-- The native structure written with pullback along Frobenius. -/
def nativePullAction (W : ProEtaleWeilSheaf k ℓ X) :
    (V (γ X).hom).obj W.carrier ⟶ W.carrier :=
  (adicUpperStarIsoLowerStarInv ℓ (γ X)).hom.app W.carrier ≫ W.str.hom

theorem changeFrobeniusModel (W : ProEtaleWeilSheaf k ℓ X) :
    ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj W).str.hom =
      (ξ (γ X).hom).app W.carrier ≫ (E (fib X)).map (nativePullAction W) := by
  unfold ProEtaleWeilSheaf.toCondensedUpperStar
    ProEtaleWeilSheaf.condensedUpperStarFrobeniusComparison
    ProEtaleWeilSheaf.condensedFrobeniusComparison nativePullAction
  transport_exact actionOfIso (γ X) W

end WeilII.ExternalProduct
