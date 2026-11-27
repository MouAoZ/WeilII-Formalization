module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.EssentialImage

namespace WeilII

open CategoryTheory

/-- For a square of left adjoints commuting up to isomorphism, with fully faithful
horizontal functors, the right-adjoint mate is invertible at any object where its target
belongs to the essential image of the first horizontal functor.

Indeed, on maps from an object of the image, composition with the mate is the bijection
given by the two adjunctions, full faithfulness and the original square. Testing the
source and the target in the image gives a two-sided inverse. This is the categorical
criterion used in specializing Katz, Appendix A.3, p. 220. -/
public theorem isIso_mate_app_of_essImage
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {J : C ⥤ E} {K : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (j : J.FullyFaithful) (k : K.FullyFaithful) (s : J ⋙ L' ≅ L ⋙ K)
    (M : D) (h : J.essImage (R'.obj (K.obj M))) :
    IsIso ((mateEquiv a b s.hom).app M) := by
  let m := (mateEquiv a b s.hom).app M
  change IsIso m
  have test (W : C) : Function.Bijective
      (fun t : J.obj W ⟶ J.obj (R.obj M) ↦ t ≫ m) := by
    let e := j.homEquiv.symm.trans (((a.homEquiv W M).symm.trans k.homEquiv).trans
      ((s.app W).symm.homFromEquiv.trans (b.homEquiv (J.obj W) (K.obj M))))
    apply (show (fun t : J.obj W ⟶ J.obj (R.obj M) ↦ t ≫ m) = e from ?_) ▸ e.bijective
    funext t
    obtain ⟨u, rfl⟩ := j.map_surjective t
    apply (b.homEquiv _ _).symm.injective
    change L'.map (J.map u ≫ m) ≫ b.counit.app _ =
      (b.homEquiv _ _).symm (e (J.map u))
    have he : e (J.map u) = b.homEquiv _ _
        (s.hom.app W ≫ K.map ((a.homEquiv _ _).symm u)) := by
      simp [e, Functor.FullyFaithful.homEquiv, Iso.homFromEquiv]
    rw [he, Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, mateEquiv_counit a b s.hom M, K.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (· ≫ K.map (a.counit.app M)) (s.hom.naturality u)
  obtain ⟨W, ⟨e⟩⟩ := h
  obtain ⟨t, ht⟩ := (test W).surjective e.hom
  change t ≫ m = e.hom at ht
  refine ⟨e.inv ≫ t, ?_, ?_⟩
  · apply (test (R.obj M)).injective
    change (m ≫ e.inv ≫ t) ≫ m = 𝟙 _ ≫ m
    simp only [Category.assoc, ht, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, ht, Iso.inv_hom_id]

end WeilII
