module

public import WeilII.Paper.AffineHyperplaneFamily
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # The affine chart of the projective incidence family -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace

universe u

/-- The chart with leading coordinate one identifies the affine inverse image in Zhang,
Theorem 2.4 (p. 3), with the inverse image of the projective fiber of Katz, Appendix A
(p. 218). At a field-valued parameter some linear coefficient is invertible. In that
chart the two ideals have the same normalized generator, including its constant term. -/
public theorem exists_affineChart_comap_projectiveHyperplaneFiber
    (K : Type u) [Field K] (J : Type u) [Fintype J] :
    let S := Spec (CommRingCat.of K)
    let P := ℙ(Option J; S)
    let B := affineHyperplaneParameter J S
    letI : S.Over S := ⟨𝟙 S⟩
    ∃ c : 𝔸(J; S) ⟶ P, c.IsOver S ∧ IsOpenImmersion c ∧
      ∀ {X : Scheme.{u}} [IsAffine X] (v : X ⟶ 𝔸(J; S)) (A : S ⟶ B.toScheme) [A.IsOver S],
        affineHyperplaneInverseImage v A =
          (projectiveHyperplaneFiber (A ≫ B.ι)).comap (v ≫ c) := by
  classical
  intro S P B
  let o : Option J := none
  let E : {z : Option J // z ≠ o} ≃ J :=
    { toFun := fun z ↦ z.1.get (by
        rcases z with ⟨_ | j, hz⟩
        · exact (hz rfl).elim
        · rfl)
      invFun := fun z ↦ ⟨some z, by simp [o]⟩
      left_inv := by rintro ⟨_ | z, hz⟩ <;> simp_all [o]
      right_inv := fun _ ↦ rfl }
  let r := (AffineSpace.reindexIso S E).hom
  let c := r ≫ (standardOpenIso (Option J) S o).inv ≫ (standardOpen (Option J) S o).ι
  have hco : c ≫ P ↘ S = 𝔸(J; S) ↘ S := by
    change (_ ≫ _ ≫ _) ≫ ℙ(Option J; S) ↘ S = _
    rw [Category.assoc, Category.assoc, standardOpenIso_inv_ι_over]
    exact AffineSpace.reindex_over E S
  refine ⟨c, ⟨hco⟩, inferInstanceAs (IsOpenImmersion
    (r ≫ (standardOpenIso (Option J) S o).inv ≫ (standardOpen (Option J) S o).ι)), ?_⟩
  intro X _ v A _
  let H := A ≫ B.ι
  let f := v ≫ c
  let a := v ≫ 𝔸(J; S) ↘ S
  let p := a ≫ A
  let q := AffineSpace.homOfVector p (fun i ↦ v.appTop (AffineSpace.coord S i))
  let g := (𝔸(J; B.toScheme) ↘ B.toScheme) ≫ B.ι
  have hfg : f ≫ P ↘ S = a := by simp only [f, Category.assoc, hco, a]
  have hqg : q ≫ g = a ≫ H := by simp [q, g, p, H]
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp (A (IsLocalRing.closedPoint K)).2
  let D := standardOpen (Option J) S (some b)
  have hbS : ⊤ ≤ H ⁻¹ᵁ D := by
    intro x _
    change (A x).1 ∈ D
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)]
  have hq : ⊤ ≤ q ⁻¹ᵁ (g ⁻¹ᵁ D) := by
    rw [← Scheme.Hom.comp_preimage, hqg]
    exact a.preimage_mono hbS
  have hf : ⊤ ≤ f ⁻¹ᵁ standardOpen (Option J) S o := by simp [f, c]
  let C : P.affineOpens := ⟨standardOpen (Option J) S o, isAffineOpen_standardOpen _ _ _⟩
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hDB : D ≤ B.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact le_iSup (fun i : J ↦ standardOpen (Option J) S (some i)) b
  let W : 𝔸(J; B.toScheme).affineOpens := ⟨g ⁻¹ᵁ D,
    ((isAffineOpen_standardOpen _ _ _).preimage_of_isOpenImmersion B.ι hDB).preimage
      (𝔸(J; B.toScheme) ↘ B.toScheme)⟩
  have hr (i : Option J) :
      f.appLE C.1 ⊤ hf (coordRatio (Option J) S o i) =
        (i.elim 1 (fun j ↦ v.appTop (AffineSpace.coord S j))) := by
    have hcoord : f = (v ≫ r) ≫ homOfSections
        (𝔸({z : Option J // z ≠ o}; S) ↘ S) (coordOne S o) (span_range_coordOne S o) := by
      rw [homOfSections_coord_eq, Category.assoc]
    let h := hcoord.trans (comp_homOfSections _ _ _ (span_range_coordOne S o))
    rw [Scheme.Hom.appLE_congr_hom h C.1 ⊤ hf (h ▸ hf)]
    rw [homOfSections_appLE_coordRatio _ _ _ (by simp [coordOne_self])]
    cases i with
    | none => simp [o, coordOne_self]
    | some j =>
      rw [coordOne_of_ne S o ⟨some j, by simp [o]⟩]
      change (v ≫ r).appTop (AffineSpace.coord S _) = v.appTop (AffineSpace.coord S j)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      exact congrArg (fun x ↦ v.appTop x)
        (AffineSpace.reindex_appTop_coord E S ⟨some j, by simp [o]⟩)
  apply Scheme.IdealSheafData.ext_of_isAffine
  change ((affineHyperplaneFamily J S).comap q).ideal V =
    ((projectiveHyperplaneFiber H).comap f).ideal V
  rw [Scheme.IdealSheafData.ideal_comap_appLE _ q W V hq,
    Scheme.IdealSheafData.ideal_comap_appLE _ f C V hf,
    projectiveHyperplaneFiber_ideal H o (some b) hbS C le_rfl]
  change ((Scheme.Modules.homOfGlobalSection _ (affineHyperplaneSection g
    (AffineSpace.coord B.toScheme))).zeroLocus.ideal W).map _ = _
  rw [affineHyperplaneIdeal_onChart g _ b W le_rfl]
  simp only [Ideal.map_span, Set.image_singleton]
  congr 2
  simp only [affineHyperplaneChartEquation, map_add, map_sum, map_mul, Fintype.sum_option]
  have coeff (i : Option J) :
      q.appLE W.1 ⊤ hq (g.app D (coordRatio (Option J) S (some b) i)) =
        f.appLE C.1 ⊤ hf ((P ↘ S).appLE ⊤ C.1 le_top
          (H.appLE D ⊤ hbS (coordRatio (Option J) S (some b) i))) := by
    have eq : q ≫ g = (f ≫ P ↘ S) ≫ H := by rw [hfg, hqg]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    apply ConcreteCategory.congr_hom
    have base := Scheme.Hom.appLE_comp_appLE f (P ↘ S) ⊤ C.1 ⊤ le_top hf
    have par := Scheme.Hom.appLE_comp_appLE (f ≫ P ↘ S) H D ⊤ ⊤ hbS le_top
    have rhs := (congrArg (H.appLE D ⊤ hbS ≫ ·) base).trans par
    exact (Scheme.Hom.comp_appLE q g D ⊤ hq).symm.trans
      ((Scheme.Hom.appLE_congr_hom eq _ _ _ _).trans rhs.symm)
  have rest {Z : Scheme.{u}} (U : Z.Opens) (x : Γ(Z, U)) :
      Z.presheaf.map (homOfLE (le_refl U)).op x = x := by
    change (Z.presheaf.map (𝟙 _)) x = x
    rw [Z.presheaf.map_id]
    rfl
  have coord (i : J) : q.appLE W.1 ⊤ hq
      (𝔸(J; B.toScheme).presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
        (AffineSpace.coord B.toScheme i)) = v.appTop (AffineSpace.coord S i) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_top_top]
    exact AffineSpace.homOfVector_appTop_coord _ _ _
  simp only [rest]
  apply congrArg₂ (· + ·)
  · change _ = f.appLE C.1 ⊤ hf (coordRatio _ S o none) * _
    rw [hr]
    exact (coeff none).trans (one_mul _).symm
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (· * ·) ((coord i).trans (hr (some i)).symm) (coeff (some i))

end WeilII
