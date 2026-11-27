module

public import WeilII.Paper.ProjectiveIncidenceComplementStandardChart
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.TraceFormula.OrdinaryKunnethOpen

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits ProjectiveSpace

universe u

/-- The simultaneous product charts of Katz A.1–A.2, pp. 218–219, as maps into the
universal square. At every ambient point the chart maps are open immersions, the
ambient and open squares are cartesian, and the projection of the open source back
to `X` is its first projection followed by the chart inclusion. -/
public theorem exists_incidenceProductChart (k : Type u) [Field k]
    (I : Type u) [Fintype I] [Nontrivial I] {X : Scheme.{u}} :
    let S := Spec (.of k)
    let P := ℙ(I; S)
    let π := P ↘ S
    ∀ (f : X ⟶ P) (z : ↥(pullback π π)),
      let F := pullback.map (f ≫ π) π π π f (𝟙 P) (𝟙 S) (by simp) (by simp)
      let B := (projectiveHyperplaneIncidenceFamily I S).subschemeι.openComplement
      ∃ d : I,
        let U := standardOpen I S d
        let T := f ⁻¹ᵁ U
        let D := Over.mk π
        let Y := Over.mk (U.ι ≫ π)
        let X' := Over.mk ((f ∣_ U) ≫ Y.hom)
        let h : X' ⟶ Y := Over.homMk (f ∣_ U) rfl
        let j : Y ⟶ D := Over.homMk U.ι rfl
        let iY := (prod.map (𝟙 Y) j).left
        let iX := (prod.map (𝟙 X') j).left
        ∃ (y : (Y ⨯ D).left ⟶ pullback π π) (x : (X' ⨯ D).left ⟶ pullback (f ≫ π) π)
          (b : (Y ⨯ Y).left ⟶ B.toScheme) (a : (X' ⨯ Y).left ⟶ (F ⁻¹ᵁ B).toScheme),
          IsOpenImmersion y ∧ IsOpenImmersion x ∧ z ∈ Set.range y ∧
          IsPullback (prod.map h (𝟙 D)).left x y F ∧ IsPullback b iY B.ι y ∧
          IsPullback a iX (F ⁻¹ᵁ B).ι x ∧
          a ≫ (F ⁻¹ᵁ B).ι ≫ pullback.fst (f ≫ π) π = (prod.fst : X' ⨯ Y ⟶ X').left ≫ T.ι := by
  classical
  intro S P π f z F B
  have hz : pullback.fst π π z ∈ (⊤ : P.Opens) := trivial
  rw [← iSup_standardOpen I S, TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨d, hd⟩ := hz
  refine ⟨d, ?_⟩
  intro U T D Y X' h j iY iX
  let u := U.ι ≫ π
  let g := f ∣_ U
  let t := g ≫ u
  let r := pullback.map u π π π U.ι (𝟙 P) (𝟙 S) (by simp [u]) (by simp)
  let C := r ⁻¹ᵁ B
  let i := pullback.map u u u π (𝟙 _) U.ι (𝟙 S) (by simp) (by simp [u])
  let H := pullback.map t π u π g (𝟙 P) (𝟙 S) (by simp [t]) (by simp)
  have ht : t = T.ι ≫ f ≫ π := by simp [t, u, g, T, ← Category.assoc]
  let s := pullback.map t π (f ≫ π) π T.ι (𝟙 P) (𝟙 S) (by simp [ht]) (by simp)
  have rSq : IsPullback (pullback.fst u π) r U.ι (pullback.fst π π) := by
    apply IsPullback.of_bot _ (by simp [r]) (IsPullback.of_hasPullback π π)
    simpa [r, u] using IsPullback.of_hasPullback u π
  have sSq : IsPullback (pullback.fst t π) s T.ι (pullback.fst (f ≫ π) π) := by
    apply IsPullback.of_bot _ (by simp [s]) (IsPullback.of_hasPullback (f ≫ π) π)
    simpa [s, ← ht] using IsPullback.of_hasPullback t π
  have family : IsPullback H s r F := by
    apply IsPullback.of_right _ _ rSq
    · simpa [H, F] using sSq.paste_horiz (isPullback_morphismRestrict f U)
    · apply pullback.hom_ext <;> simp [H, r, F, s, T, g]
  obtain ⟨σ, e, _, he, charts⟩ := projectiveIncidenceComplement_standardChart k I d
  obtain ⟨σT, _, hpr, hσ, _, _⟩ := charts T.toScheme g
  change e.hom ≫ i = C.ι ≫ σ.hom at he
  change σT.hom ≫ H = H ≫ σ.hom at hσ
  change σT.hom ≫ pullback.fst t π = pullback.fst t π at hpr
  let EY := Over.prodLeftIsoPullback Y D ≪≫ σ.symm
  let EX := Over.prodLeftIsoPullback X' D ≪≫ σT.symm
  let EV := Over.prodLeftIsoPullback Y Y ≪≫ e.symm
  let y := EY.hom ≫ r
  let x := EX.hom ≫ s
  let b := EV.hom ≫ (r ∣_ B)
  have : IsOpenImmersion r := MorphismProperty.of_isPullback rSq inferInstance
  have : IsOpenImmersion s := MorphismProperty.of_isPullback sSq inferInstance
  have natural {A B C D : Over S} (m : A ⟶ C) (n : B ⟶ D) :
      (prod.map m n).left ≫ (Over.prodLeftIsoPullback C D).hom =
        (Over.prodLeftIsoPullback A B).hom ≫
          pullback.map A.hom B.hom C.hom D.hom m.left n.left (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [← Over.comp_left]
  have i_comp : iY ≫ (Over.prodLeftIsoPullback Y D).hom =
      (Over.prodLeftIsoPullback Y Y).hom ≫ i := natural (𝟙 Y) j
  have H_comp : (prod.map h (𝟙 D)).left ≫ (Over.prodLeftIsoPullback Y D).hom =
      (Over.prodLeftIsoPullback X' D).hom ≫ H := natural h (𝟙 D)
  have q : IsPullback (prod.map h (𝟙 D)).left x y F := by
    apply family.of_iso' EX EY (Iso.refl _) (Iso.refl _)
    · change _ ≫ σT.inv ≫ H = _ ≫ (Over.prodLeftIsoPullback Y D).hom ≫ σ.inv
      rw [← Category.assoc _ (Over.prodLeftIsoPullback Y D).hom, H_comp, Category.assoc]
      congr 1
      rw [Iso.inv_comp_eq]
      simpa only [Iso.hom_inv_id, Category.comp_id] using ((reassoc_of% hσ) σ.inv).symm
    · simp [x]
    · simp [y]
    · simp
  have qb : IsPullback b iY B.ι y := by
    apply (isPullback_morphismRestrict r B).of_iso' EV (Iso.refl _) EY (Iso.refl _)
    · simp [b]
    · change _ ≫ e.inv ≫ C.ι = iY ≫ (Over.prodLeftIsoPullback Y D).hom ≫ σ.inv
      rw [← Category.assoc iY, i_comp, Category.assoc]
      congr 1
      rw [Iso.inv_comp_eq, ← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp [y]
  have prodSq := (ProEtale.CondensedRing.isPullback_prodMap_prodMap h j).map (Over.forget S)
  have outer : IsPullback ((prod.map h (𝟙 Y)).left ≫ b) iX B.ι (x ≫ F) := by
    rw [← q.w]
    exact prodSq.paste_horiz qb
  let globalSq := isPullback_morphismRestrict F B
  let a := globalSq.lift ((prod.map h (𝟙 Y)).left ≫ b) (iX ≫ x)
    (outer.w.trans (Category.assoc iX x F).symm)
  have ha : a ≫ (F ⁻¹ᵁ B).ι = iX ≫ x := globalSq.lift_snd ..
  have qa : IsPullback a iX (F ⁻¹ᵁ B).ι x := by
    apply IsPullback.of_right _ ha globalSq
    rwa [show a ≫ (F ∣_ B) = _ from globalSq.lift_fst ..]
  refine ⟨y, x, b, a, inferInstanceAs (IsOpenImmersion (EY.hom ≫ r)),
    inferInstanceAs (IsOpenImmersion (EX.hom ≫ s)), ?_, q, qb, qa, ?_⟩
  · obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback rSq
      (⟨pullback.fst π π z, hd⟩ : U) z rfl
    exact ⟨EY.inv w, by simpa [y, Scheme.Hom.comp_apply] using hw⟩
  · rw [← Category.assoc, ha, Category.assoc]
    have hfst : σT.inv ≫ pullback.fst t π = pullback.fst t π := by
      rw [Iso.inv_comp_eq, hpr]
    simp only [x, EX, Iso.trans_hom, Iso.symm_hom, Category.assoc, sSq.w.symm]
    rw [reassoc_of% hfst]
    change iX ≫ (Over.prodLeftIsoPullback X' D).hom ≫ pullback.fst X'.hom D.hom ≫ T.ι = _
    rw [Over.prodLeftIsoPullback_hom_fst_assoc, ← Category.assoc]
    simp [iX, ← Over.comp_left]

end WeilII
