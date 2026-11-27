module

public import WeilConjectures.TraceFormula.OrdinaryKunnethDevissage

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.Scheme
open CategoryTheory Limits MonoidalCategory Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

attribute [local instance] boundedConstructibleBraiding
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

set_option backward.isDefEq.respectTransparency false in
/-- The direct image of the product with an open-extended unit is supported on the
same open in the parameter. Apply the boundary-vanishing theorem of ordinary Künneth
(SGA 4½, Théorèmes de finitude, Cor. 1.11), then the open–closed triangle. -/
public theorem boundedOpenUnitProductSupport (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y V S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (h : X ⟶ Y) (j : V ⟶ S) [IsOpenImmersion j.left]
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (boundedConstructibleLowerShriek ℓ (prod.map j (𝟙 Y))).essImage
      ((boundedConstructibleLowerStar ℓ (prod.map (𝟙 S) h)).obj
        ((boundedConstructibleLowerShriek ℓ (prod.map j (𝟙 X))).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (prod.snd : V ⨯ X ⟶ X)).obj B))) := by

  let i := overClosedComplement j
  have recov (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
      [IsSeparated T.hom] (M : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (S ⨯ T).left))
      (hz : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map i (𝟙 T))).obj M)) :
      Nonempty ((boundedConstructibleLowerShriek ℓ (prod.map j (𝟙 T))).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map j (𝟙 T))).obj M) ≅ M) := by
    have : IsOpenImmersion (prod.map j (𝟙 T)).left :=
      MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id j T).map (Over.forget _))
        (inferInstanceAs (IsOpenImmersion j.left))
    have : IsClosedImmersion (prod.map i (𝟙 T)).left :=
      MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id i T).map (Over.forget _))
        (inferInstanceAs (IsClosedImmersion (overClosedComplement j).left))
    obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed_boundedConstructible ℓ
      (isCompl_range_prodMap_id i j (isCompl_range_overClosedComplement j)).symm M
    have : IsIso ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ
        (prod.map j (𝟙 T))).counit.app M) := (Triangle.isZero₃_iff_isIso₁ _ hδ).mp
      ((boundedConstructibleLowerStar ℓ (prod.map i (𝟙 T))).map_isZero hz)
    exact ⟨asIso ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ
      (prod.map j (𝟙 T))).counit.app M)⟩
  let L : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left) := 𝟙_ _
  let J := (boundedConstructibleLowerShriek ℓ j).obj L
  let E := externalProduct ℓ J B
  let jX := prod.map j (𝟙 X)
  let iX := prod.map i (𝟙 X)
  let p := (prod.fst : S ⨯ X ⟶ S)
  let q := (prod.snd : S ⨯ X ⟶ X)
  have hg : Disjoint (Set.range j.left.base) (Set.range (iX ≫ p).left.base) := by
    rw [show iX ≫ p = prod.fst ≫ i by simp [iX, p], Over.comp_left, Scheme.Hom.comp_base,
      TopCat.coe_comp]
    exact (isCompl_range_overClosedComplement j).disjoint.symm.mono_right
      (Set.range_comp_subset_range _ _)
  have hz := (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j _ hg L).of_iso
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ iX p).symm.app J ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ _).mapIso
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app L))
  have hzE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ iX).obj E) := by
    refine IsZero.of_iso ?_ (Functor.Monoidal.μIso _ _ _).symm
    exact isZero_tensorObj_of_isZero_left hz _
  obtain ⟨e⟩ := recov X E hzE
  let eL := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).mapIso
    ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app L) ≪≫
    (asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app L)).symm
  let square : CommSq (prod.fst : V ⨯ X ⟶ V) jX j p := ⟨by simp [p, jX]⟩
  let ep := (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ square).app J ≪≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : V ⨯ X ⟶ V)).mapIso eL ≪≫
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : V ⨯ X ⟶ V))).symm
  let eq := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ jX q).symm.app B ≪≫
    eqToIso (show (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (jX ≫ q)).obj B =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : V ⨯ X ⟶ X)).obj B by simp [jX, q])
  let eR : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jX).obj E ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : V ⨯ X ⟶ X)).obj B :=
    (Functor.Monoidal.μIso _ _ _).symm ≪≫ tensorIso ep eq ≪≫ λ_ _
  let eE := (boundedConstructibleLowerShriek ℓ jX).mapIso eR.symm ≪≫ e
  obtain ⟨eH⟩ := recov Y _ (isZero_upperStar_lowerStar_externalProduct_lowerShriek ℓ h B j L)
  exact ⟨_, ⟨eH ≪≫ (boundedConstructibleLowerStar ℓ (prod.map (𝟙 S) h)).mapIso eE.symm⟩⟩

end WeilII
