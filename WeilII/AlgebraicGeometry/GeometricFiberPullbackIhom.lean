module

public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.Dual
import WeilConjectures.WeilSheaf.IhomLisse.UpperStar
import WeilConjectures.WeilSheaf.CondensedModelDescent

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace WeilII

universe u

private theorem pullbackPairing {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (P : C ⥤ D) (F : D ⥤ D) [P.LaxMonoidal] [F.LaxMonoidal]
    (s : P ⋙ F ≅ P) [NatTrans.IsMonoidal s.hom] {A B N : C} (e : A ⊗ B ⟶ N) :
    (s.hom.app A ⊗ₘ s.hom.app B) ≫ μ P A B ≫ P.map e =
      μ F (P.obj A) (P.obj B) ≫ F.map (μ P A B ≫ P.map e) ≫ s.hom.app N := by
  have ht := NatTrans.IsMonoidal.tensor (τ := s.hom) A B
  rw [← Category.assoc, ← ht]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.map_comp, Category.assoc]
  rw [← s.hom.naturality e]
  rfl

private theorem pullbackPairingOfEq {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (P : C ⥤ D) (F : D ⥤ D)
    [P.LaxMonoidal] [F.LaxMonoidal] (s : P ⋙ F ≅ P) [NatTrans.IsMonoidal s.hom]
    {A B N : C} (e : A ⊗ B ⟶ N)
    {sA : F.obj (P.obj A) ⟶ P.obj A} {sB : F.obj (P.obj B) ⟶ P.obj B}
    {sN : F.obj (P.obj N) ⟶ P.obj N} {v : P.obj A ⊗ P.obj B ⟶ P.obj N}
    (ha : sA = s.hom.app A) (hb : sB = s.hom.app B) (hn : sN = s.hom.app N)
    (hv : v = μ P A B ≫ P.map e) :
    (sA ⊗ₘ sB) ≫ v = μ F (P.obj A) (P.obj B) ≫ F.map v ≫ sN := by
  subst sA sB sN v
  exact pullbackPairing P F s e

private theorem pullbackIhomCommOfPairing {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (ℓ : ℕ) [Fact ℓ.Prime] (M N : AdicSheaf ℓ Y)
    (s : (p)^*[WeilCoefficients ℓ] ⋙ (b.inv)_*[WeilCoefficients ℓ] ≅ (p)^*[WeilCoefficients ℓ])
    [NatTrans.IsMonoidal s.hom]
    (sH : (b.inv)_*ᵃ[ℓ].obj ((p)^*ᵃ[ℓ].obj ((AdicSheaf.ihom M).obj N)) ≅
      (p)^*ᵃ[ℓ].obj ((AdicSheaf.ihom M).obj N))
    (sM : (b.inv)_*ᵃ[ℓ].obj ((p)^*ᵃ[ℓ].obj M) ≅ (p)^*ᵃ[ℓ].obj M)
    (sN : (b.inv)_*ᵃ[ℓ].obj ((p)^*ᵃ[ℓ].obj N) ≅ (p)^*ᵃ[ℓ].obj N)
    (hH : sH.hom.hom = s.hom.app ((AdicSheaf.ihom M).obj N).X)
    (hM : sM.hom.hom = s.hom.app M.X) (hN : sN.hom.hom = s.hom.app N.X) :
    (b.inv)_*ᵃ[ℓ].map (adicUpperStarIhomComparison ℓ p M N) ≫ (ihomStr ℓ b sM sN).hom =
      sH.hom ≫ adicUpperStarIhomComparison ℓ p M N := by
  apply ihomStr_comm_of_pairing b
  have he := uncurryHom_adicUpperStarIhomComparison p M N
  dsimp only [Mod.uncurryHom] at he
  exact pullbackPairingOfEq (p)^*[WeilCoefficients ℓ] (b.inv)_*[WeilCoefficients ℓ] s
    (Mod.evaluation M N) hH hM hN he

private noncomputable def adicDescent {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] :
    (p)^*ᵃ[ℓ] ⋙ (b.inv)_*ᵃ[ℓ] ≅ (p)^*ᵃ[ℓ] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv ℓ b).symm ≪≫
    (adicUpperStarComp ℓ b.hom p).symm ≪≫ adicUpperStarCongr ℓ hb

private noncomputable def sheafDescent {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] :
    (p)^*[WeilCoefficients ℓ] ⋙ (b.inv)_*[WeilCoefficients ℓ] ≅ (p)^*[WeilCoefficients ℓ] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv (WeilCoefficients ℓ) b).symm ≪≫
    (upperStarComp (WeilCoefficients ℓ) b.hom p).symm ≪≫ upperStarCongr (WeilCoefficients ℓ) hb

private instance {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X) (hb : b.hom ≫ p = p)
    (ℓ : ℕ) [Fact ℓ.Prime] : NatTrans.IsMonoidal (sheafDescent p b hb ℓ).hom :=
  NatTrans.isMonoidal_trans_hom _ _
    (NatTrans.isMonoidal_isoWhiskerLeft_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance))
    (NatTrans.isMonoidal_trans_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance) inferInstance)

private theorem adicDescent_hom_parts {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] (A : AdicSheaf ℓ Y) :
    ((adicDescent p b hb ℓ).hom.app A).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) b).inv.app ((p)^*ᵃ[ℓ].obj A).X ≫
      (upperStarComp _ b.hom p).inv.app A.X ≫ (upperStarCongr _ hb).hom.app A.X := by
  simp only [adicDescent, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Mod.comp_hom',
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom]
  rfl

private theorem tripleApp {C D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {F G : D ⥤ D} {H : C ⥤ D} (e : G ≅ F) (s : H ≅ P ⋙ G) (t : H ≅ P) (A : C) :
    (Functor.isoWhiskerLeft P e.symm ≪≫ s.symm ≪≫ t).hom.app A =
      e.inv.app (P.obj A) ≫ s.inv.app A ≫ t.hom.app A := rfl

private theorem sheafDescent_eq {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] :
    sheafDescent p b hb ℓ =
      Functor.isoWhiskerLeft (p)^*[WeilCoefficients ℓ] (upperStarIsoLowerStarInv (WeilCoefficients ℓ) b).symm ≪≫
      (upperStarComp (WeilCoefficients ℓ) b.hom p).symm ≪≫ upperStarCongr (WeilCoefficients ℓ) hb := rfl

private theorem sheafDescent_hom_parts {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] (A : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} ℓ)) :
    (sheafDescent p b hb ℓ).hom.app A =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) b).inv.app ((p)^*[WeilCoefficients ℓ].obj A) ≫
      (upperStarComp _ b.hom p).inv.app A ≫ (upperStarCongr _ hb).hom.app A :=
  (congrArg (fun i ↦ i.hom.app A) (sheafDescent_eq p b hb ℓ)).trans <|
  tripleApp (p)^*[WeilCoefficients.{u} ℓ] (upperStarIsoLowerStarInv _ b)
    (upperStarComp _ b.hom p) (upperStarCongr _ hb) A

-- Keep the first component abstract while identifying the two carriers of pullback.
private theorem compThreeCongr {C : Type*} [Category* C] {A B D E : C}
    {f f' : A ⟶ B} {g g' : B ⟶ D} {j j' : D ⟶ E} (hf : f = f') (hg : g = g') (hj : j = j') :
    f ≫ g ≫ j = f' ≫ g' ≫ j' := by rw [hf, hg, hj]

private theorem appOnAdicCarrier {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X) (ℓ : ℕ)
    [Fact ℓ.Prime] (A : AdicSheaf ℓ Y)
    (τ : (b.inv)_*[WeilCoefficients ℓ] ⟶ (b.hom)^*[WeilCoefficients ℓ]) :
    τ.app ((p)^*ᵃ[ℓ].obj A).X = τ.app ((p)^*[WeilCoefficients ℓ].obj A.X) := rfl

private theorem adicDescent_hom {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] (A : AdicSheaf ℓ Y) :
    ((adicDescent p b hb ℓ).hom.app A).hom = (sheafDescent p b hb ℓ).hom.app A.X :=
  (adicDescent_hom_parts p b hb ℓ A).trans <|
    (compThreeCongr (appOnAdicCarrier p b ℓ A (upperStarIsoLowerStarInv _ b).inv)
      (rfl : (upperStarComp (WeilCoefficients ℓ) b.hom p).inv.app A.X = _)
      (rfl : (upperStarCongr (WeilCoefficients ℓ) hb).hom.app A.X = _)).trans
        (sheafDescent_hom_parts p b hb ℓ A.X).symm

private theorem pulledIhomComm {X Y : Scheme.{u}} (p : X ⟶ Y) (b : X ≅ X)
    (hb : b.hom ≫ p = p) (ℓ : ℕ) [Fact ℓ.Prime] (M N : AdicSheaf ℓ Y) :
    let str := adicDescent p b hb ℓ
    (b.inv)_*ᵃ[ℓ].map (adicUpperStarIhomComparison ℓ p M N) ≫
      (ihomStr ℓ b (str.app M) (str.app N)).hom =
      (str.app ((AdicSheaf.ihom M).obj N)).hom ≫ adicUpperStarIhomComparison ℓ p M N :=
  pullbackIhomCommOfPairing p b ℓ M N (sheafDescent p b hb ℓ) _ _ _
    (adicDescent_hom p b hb ℓ _) (adicDescent_hom p b hb ℓ M) (adicDescent_hom p b hb ℓ N)

/-- Geometric pullback of an arithmetic internal Hom is the internal Hom of the
two descended Weil sheaves. Weakly étale pullback preserves internal Hom. The
underlying evaluation pairing respects descent because the canonical Frobenius
comparison for the projection is monoidal. -/
public theorem geometricFiberPullbackIhom
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] (M N : AdicSheaf ℓ Z) :
    let P := ProEtaleWeilSheaf.geometricFiberPullback k ℓ Z
    Nonempty (P.obj ((AdicSheaf.ihom M).obj N) ≅ ProEtaleWeilSheaf.ihom k ℓ Z (P.obj M) (P.obj N)) := by
  let a := Z ↘ Spec (.of k)
  let p := a.geometricFiberProj
  let b := a.geometricGaloisFrobenius.asIso
  have : WeaklyEtale p := inferInstanceAs (WeaklyEtale a.geometricFiberProj)
  let P := ProEtaleWeilSheaf.geometricFiberPullback k ℓ Z
  let T := ProEtaleWeilSheaf.ihom k ℓ Z (P.obj M) (P.obj N)
  have hi := adicUpperStarIhomComparison_eq_of_weaklyEtale p M N
  have : IsIso (adicUpperStarIhomComparison ℓ p M N) := by rw [hi]; infer_instance
  let e := asIso (adicUpperStarIhomComparison ℓ p M N)
  have h := pulledIhomComm p b (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj a) ℓ M N
  have hk (A : AdicSheaf ℓ Z) := ProEtaleWeilSheaf.geometricFiberPullback_obj_str k ℓ Z A
  refine ⟨Endofunctor.IsoAlgebra.isoMk (K := P.obj ((AdicSheaf.ihom M).obj N)) (K' := T) e ?_⟩
  rw [← Endofunctor.IsoAlgebra.str_hom, ← Endofunctor.IsoAlgebra.str_hom]
  change _ ≫ (ProEtaleWeilSheaf.ihom k ℓ Z (P.obj M) (P.obj N)).str.hom = _
  rw [ProEtaleWeilSheaf.ihom_str, hk, hk, hk]
  exact h

end WeilII
