module

public import WeilII.AlgebraicGeometry.TensorInverseComparisonEvaluation
import WeilII.AlgebraicGeometry.EtaleKummerTateSheafReduction

/-! # Naturality of the comparison on the onefold inverse tensor power -/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace WeilII

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E] [Category* J]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory J]

private abbrev pairing (F : C ⥤ E) [F.Monoidal] {X Y : C} (v : X ⊗ Y ⟶ 𝟙_ C) :=
  μ F X Y ≫ F.map v ≫ η F

private theorem pairing_nat {F G : C ⥤ E} [F.Monoidal] [G.Monoidal] (s : F ⟶ G)
    [NatTrans.IsMonoidal s] {X Y : C} (v : X ⊗ Y ⟶ 𝟙_ C) :
    (s.app X ⊗ₘ s.app Y) ≫ pairing G v = pairing F v := by
  have hu : s.app (𝟙_ C) ≫ η G = η F := by
    apply (cancel_epi (ε F)).1
    rw [← Category.assoc, NatTrans.IsMonoidal.unit, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  unfold pairing
  rw [← NatTrans.IsMonoidal.tensor_assoc, ← s.naturality_assoc, hu]

private theorem pairing_map (H : E ⥤ J) [H.Monoidal] {U V X Y : E} {u : U ⊗ V ⟶ 𝟙_ E}
    {v : X ⊗ Y ⟶ 𝟙_ E} {r : U ⟶ X} {p : V ⟶ Y} (h : (r ⊗ₘ p) ≫ v = u) :
    (H.map r ⊗ₘ H.map p) ≫ pairing H v = pairing H u := by
  unfold pairing
  rw [μ_natural_assoc, ← H.map_comp_assoc, h]

private theorem pairing_comp (F : C ⥤ E) [F.Monoidal] (H : E ⥤ J) [H.Monoidal]
    {X Y : C} (v : X ⊗ Y ⟶ 𝟙_ C) : pairing (F ⋙ H) v = pairing H (pairing F v) := by
  simp only [pairing, Functor.comp_map, comp_μ, comp_η, Functor.map_comp, Category.assoc]

private noncomputable abbrev oneEval {L : C} (e : TensorInverse L) : e.zpow (-1) ⊗ L ≅ 𝟙_ C :=
  whiskerRightIso (ρ_ e.obj) L ≪≫ e.leftIso

private noncomputable abbrev negComparison {L : C} {M : D} (e : TensorInverse L) (d : TensorInverse M)
    (F : C ⥤ E) [F.Monoidal] (G : D ⥤ E) [G.Monoidal] (p : F.obj L ≅ G.obj M) :=
  e.zpowMapIso (d.map G) F p (-1) ≪≫ (d.zpowMapIso (d.map G) G (Iso.refl _) (-1)).symm

private theorem normalizedPairing {L : C} (w : TensorInverse L) (K : C ⥤ E) [K.Monoidal] :
    pairing K (oneEval w).hom = K.map (ρ_ w.obj).hom ▷ K.obj L ≫ pairing K w.leftIso.hom := by
  change μ K _ _ ≫ K.map ((ρ_ w.obj).hom ▷ L ≫ w.leftIso.hom) ≫ η K = _
  rw [K.map_comp, Category.assoc]
  exact (μ_natural_left_assoc K (ρ_ w.obj).hom L _).symm

omit [MonoidalCategory E] in
private theorem pasteUnitors {P Q P' Q' T U : E} (a : P ≅ T) (b : Q ≅ T)
    (c : P' ≅ U) (d : Q' ≅ U) (r : P ⟶ P') (s : Q ⟶ Q') (t : T ⟶ U)
    (h : a.hom ≫ t = r ≫ c.hom) (j : b.hom ≫ t = s ≫ d.hom) :
    (a.hom ≫ b.inv) ≫ s = r ≫ c.hom ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← j, Iso.inv_hom_id_assoc, h]

private theorem negEvaluation {L : C} {M : D} (e : TensorInverse L) (d : TensorInverse M)
    (F : C ⥤ E) [F.Monoidal] (G : D ⥤ E) [G.Monoidal] (p : F.obj L ≅ G.obj M) :
    ((negComparison e d F G p).hom ⊗ₘ p.hom) ≫ pairing G (oneEval d).hom = pairing F (oneEval e).hom := by
  let a := (e.map F).ofIso p
  let b := (d.map G).ofIso (Iso.refl _)
  let t := d.map G
  let k : F.obj e.obj ⟶ G.obj d.obj := (a.objIso t).hom ≫ (b.objIso t).inv
  have hk : k ▷ G.obj M ≫ pairing G d.leftIso.hom =
      F.obj e.obj ◁ p.inv ≫ pairing F e.leftIso.hom := by
    simpa only [TensorInverse.ofIso, TensorInverse.map, Iso.trans_hom, Iso.symm_hom,
      Iso.refl_inv, whiskerLeftIso_hom, whiskerLeft_id, Category.id_comp, Functor.mapIso_hom,
      Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_inv, Category.assoc, a, b, t, k, pairing]
      using tensorInverse_comparison_leftEvaluation a b t
  have raw : (k ⊗ₘ p.hom) ≫ pairing G d.leftIso.hom = pairing F e.leftIso.hom := by
    rw [tensorHom_def', Category.assoc, hk, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]
  have hr : (negComparison e d F G p).hom ≫ G.map (ρ_ d.obj).hom = F.map (ρ_ e.obj).hom ≫ k := by
    have hn := tensorPowNatMapIso_one_unitor F (a.objIso t)
    have hm := tensorPowNatMapIso_one_unitor G (b.objIso t)
    change ((TensorInverse.tensorPowNatMapIso F (a.objIso t) 1).hom ≫
      (TensorInverse.tensorPowNatMapIso G (b.objIso t) 1).inv) ≫ _ = _
    exact pasteUnitors _ _ _ _ _ _ _ hn hm
  erw [normalizedPairing d G, normalizedPairing e F, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id, hr,
    ← Category.id_comp p.hom, ← tensorHom_comp_tensorHom_assoc, raw, tensorHom_id]
  rfl

/-- A square of monoidal comparisons commuting on the positive lines commutes on the onefold
inverse tensor powers. Tensor with the positive comparison and cancel the common evaluation. -/
theorem tensorInverse_negativeComparison_naturality {L : C} {M : D} (e : TensorInverse L) (d : TensorInverse M)
    (F : C ⥤ E) [F.Monoidal] (G : D ⥤ E) [G.Monoidal] (H : E ⥤ J) [H.Monoidal]
    (F' : C ⥤ J) [F'.Monoidal] (G' : D ⥤ J) [G'.Monoidal]
    (s : F ⋙ H ≅ F') [NatTrans.IsMonoidal s.hom] (t : G ⋙ H ≅ G') [NatTrans.IsMonoidal t.hom]
    (p : F.obj L ≅ G.obj M) (q : F'.obj L ≅ G'.obj M)
    (hp : H.map p.hom ≫ t.hom.app M = s.hom.app L ≫ q.hom) :
    H.map (e.zpowMapIso (d.map G) F p (-1) ≪≫ (d.zpowMapIso (d.map G) G (Iso.refl _) (-1)).symm).hom ≫
        t.hom.app (d.zpow (-1)) = s.hom.app (e.zpow (-1)) ≫
      (e.zpowMapIso (d.map G') F' q (-1) ≪≫ (d.zpowMapIso (d.map G') G' (Iso.refl _) (-1)).symm).hom := by
  let x := negComparison e d F G p
  let y := negComparison e d F' G' q
  let z := H.map p.hom ≫ t.hom.app M
  have h₁ := pairing_map H (negEvaluation e d F G p)
  rw [← pairing_comp, ← pairing_comp] at h₁
  have h₂ := negEvaluation e d F' G' q
  have ht := pairing_nat t.hom (oneEval d).hom
  have hs := pairing_nat s.hom (oneEval e).hom
  let u := H.map x.hom ≫ t.hom.app _
  let v := s.hom.app _ ≫ y.hom
  have heq : (u ⊗ₘ z) ≫ pairing G' (oneEval d).hom = (v ⊗ₘ z) ≫ pairing G' (oneEval d).hom := by
    calc
      _ = pairing (F ⋙ H) (oneEval e).hom := by
        dsimp only [u, z]
        rw [← tensorHom_comp_tensorHom_assoc, ht]
        exact h₁
      _ = _ := by
        dsimp only [v, z]
        rw [hp, ← tensorHom_comp_tensorHom_assoc, h₂, hs]
  have hz := (cancel_mono (pairing G' (oneEval d).hom)).mp heq
  rw [tensorHom_def, tensorHom_def] at hz
  have hw := (cancel_mono (_ ◁ z)).mp hz
  let invL := ((e.map F).map H)
  exact (tensorRightEquivalenceOfTensorIso invL.rightIso invL.leftIso).functor.map_injective hw

end WeilII
