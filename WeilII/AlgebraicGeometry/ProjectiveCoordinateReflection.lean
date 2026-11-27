module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilII.AlgebraicGeometry.ProjectiveChartRatiosPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-! # A relative change of homogeneous coordinates on projective space -/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits ProjectiveSpace

universe u

/-- The homogeneous reflection with distinguished coordinate `a`. -/
@[expose] public def chartReflection {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : I) (c s : I → R) (i : I) : R :=
  if i = a then s a + ∑ j ∈ Finset.univ.erase a, c j * s j else -s i

private theorem reflect_twice {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : I) (c s : I → R) : chartReflection a c (chartReflection a c s) = s := by
  funext i
  by_cases hi : i = a
  · subst i
    have h : (∑ j ∈ Finset.univ.erase a, c j * chartReflection a c s j) =
        -(∑ j ∈ Finset.univ.erase a, c j * s j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj ↦ by simp [chartReflection, (Finset.mem_erase.mp hj).1]
    simp only [chartReflection, ↓reduceIte] at h ⊢
    rw [h, add_neg_cancel_right]
  · simp [chartReflection, hi]

private theorem reflect_span_le {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : I) (c s : I → R) :
    Ideal.span (Set.range (chartReflection a c s)) ≤ Ideal.span (Set.range s) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h (j) : s j ∈ Ideal.span (Set.range s) := Ideal.subset_span ⟨j, rfl⟩
  unfold chartReflection
  split
  · exact add_mem (h a) (sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ (h j))
  · exact neg_mem (h i)

/-- The reflected homogeneous coordinates still generate the unit ideal. -/
public theorem chartReflection_span {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : I) (c s : I → R) (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range (chartReflection a c s)) = ⊤ := by
  have h := reflect_span_le a c (chartReflection a c s)
  rwa [reflect_twice, hs, top_le_iff] at h

private theorem reflect_map {I R A : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing A]
    (f : R →+* A) (a : I) (c s : I → R) (i : I) :
    f (chartReflection a c s i) = chartReflection a (fun j ↦ f (c j)) (fun j ↦ f (s j)) i := by
  by_cases h : i = a <;> simp [chartReflection, h]

private theorem reflect_scale {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : I) (c s : I → R) (r : R) (i : I) :
    chartReflection a c (fun j ↦ r * s j) i = r * chartReflection a c s i := by
  by_cases h : i = a
  · simp only [chartReflection, h, ite_true, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intros
    ring
  · simp [chartReflection, h]

private noncomputable def reflectedHom {I : Type u} [Fintype I] [DecidableEq I]
    {S X : Scheme.{u}} (g : X ⟶ S) (a : I) (c s : I → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) : X ⟶ ℙ(I; S) :=
  homOfSections g (chartReflection a c s) (chartReflection_span a c s hs)

private theorem comp_reflectedHom {I : Type u} [Fintype I] [DecidableEq I]
    {S X Y : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S) (a : I) (c s : I → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    f ≫ reflectedHom g a c s hs = reflectedHom (f ≫ g) a
      (fun j ↦ f.appTop (c j)) (fun j ↦ f.appTop (s j)) (span_range_appTop_eq_top f hs) := by
  rw [reflectedHom, comp_homOfSections, reflectedHom]
  congr 1
  exact funext (reflect_map f.appTop.hom a c s)

private theorem normalizedTuple {I : Type u} {S X : Scheme.{u}} (g : X ⟶ S)
    (s : I → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤) (b : I)
    (hb : ⊤ ≤ homOfSections g s hs ⁻¹ᵁ standardOpen I S b) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, (homOfSections g s hs).appLE _ ⊤ hb (coordRatio I S b i) =
      u * s i := by
  have hu := Scheme.isUnit_of_basicOpen_eq_top (s b) (by
    rwa [← homOfSections_preimage_standardOpen g s hs b, eq_top_iff])
  let u := hu.unit⁻¹
  let t (j : I) := (u : Γ(X, ⊤)) * s j
  have ht : t b = 1 := by
    change ↑hu.unit⁻¹ * s b = 1
    nth_rw 2 [← hu.unit_spec]
    exact hu.unit.inv_mul
  have hspan := (Ideal.eq_top_iff_one (Ideal.span (Set.range t))).mpr
    (Ideal.subset_span (show 1 ∈ Set.range t from ⟨b, ht⟩))
  have eq := homOfSections_eq_of_unit_mul g u hs hspan (fun _ ↦ rfl)
  refine ⟨u, fun i ↦ ?_⟩
  rw [Scheme.Hom.appLE_congr_hom eq _ _ hb (eq ▸ hb)]
  exact homOfSections_appLE_coordRatio _ _ hspan ht i _

private theorem reflectedHom_congr {I : Type u} [Fintype I] [DecidableEq I] {S X : Scheme.{u}}
    (g : X ⟶ S) (a : I) (c s t : I → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (ht : Ideal.span (Set.range t) = ⊤)
    (eq : homOfSections g s hs = homOfSections g t ht) :
    reflectedHom g a c s hs = reflectedHom g a c t ht := by
  let y := homOfSections g s hs
  let W (b : I) := y ⁻¹ᵁ standardOpen I S b
  apply Scheme.Opens.hom_ext_of_iSup_eq_top W (y.iSup_preimage_eq_top (iSup_standardOpen I S))
  intro b
  let f := (W b).ι
  have land : ⊤ ≤ (f ≫ y) ⁻¹ᵁ standardOpen I S b := fun x _ ↦ x.2
  have coords (v : I → Γ(X, ⊤)) (hv : Ideal.span (Set.range v) = ⊤)
      (ey : y = homOfSections g v hv) :
      ∃ u : Γ(W b, ⊤)ˣ, ∀ i, (f ≫ y).appLE _ ⊤ land (coordRatio I S b i) =
        u * f.appTop (v i) := by
    have ef := (congrArg (f ≫ ·) ey).trans (comp_homOfSections f g v hv)
    rw [Scheme.Hom.appLE_congr_hom ef _ _ land (ef ▸ land)]
    exact normalizedTuple _ _ _ b _
  obtain ⟨u, hu⟩ := coords s hs rfl
  obtain ⟨v, hv⟩ := coords t ht eq
  rw [comp_reflectedHom, comp_reflectedHom, reflectedHom, reflectedHom]
  refine homOfSections_eq_of_unit_mul _ (v⁻¹ * u) _ _ fun i ↦ ?_
  let r := (↑(v⁻¹ * u) : Γ(W b, ⊤))
  have scale : (fun j ↦ f.appTop (t j)) = fun j ↦ r * f.appTop (s j) := by
    funext j
    have h := (hv j).symm.trans (hu j)
    simpa [r, ← mul_assoc] using congrArg ((↑v⁻¹ : Γ(W b, ⊤)) * ·) h
  rw [scale]
  exact reflect_scale _ _ _ _ _


/-- Reflect the coordinates of a projective morphism with coefficients on the source.
The test-morphism formula holds for every tuple presenting the pullback. -/
private theorem exists_reflectedHom {I : Type u} [Fintype I] [DecidableEq I]
    {S X : Scheme.{u}} [IsAffine S] (a : I) (y : X ⟶ ℙ(I; S)) (c : I → Γ(X, ⊤)) :
    ∃ z : X ⟶ ℙ(I; S), z ≫ ℙ(I; S) ↘ S = y ≫ ℙ(I; S) ↘ S ∧
      ∀ {T : Scheme.{u}} (f : T ⟶ X) (s : I → Γ(T, ⊤)) (hs : Ideal.span (Set.range s) = ⊤),
        f ≫ y = homOfSections (f ≫ y ≫ ℙ(I; S) ↘ S) s hs →
        f ≫ z = reflectedHom (f ≫ y ≫ ℙ(I; S) ↘ S) a (fun j ↦ f.appTop (c j)) s hs := by
  let g := y ≫ ℙ(I; S) ↘ S
  let W (b : I) := y ⁻¹ᵁ standardOpen I S b
  have cover : ⨆ b, W b = ⊤ := y.iSup_preimage_eq_top (iSup_standardOpen I S)
  have pres (b : I) : ∃ (v : I → Γ(W b, ⊤)) (hv : Ideal.span (Set.range v) = ⊤),
      (W b).ι ≫ y = homOfSections ((W b).ι ≫ g) v hv := by
    obtain ⟨hv, e⟩ := homOfChartRatios ((W b).ι ≫ y) b (fun x _ ↦ x.2)
    exact ⟨_, hv, by simpa only [Category.assoc] using e⟩
  choose v hv eqv using pres
  let F (b : I) := reflectedHom ((W b).ι ≫ g) a (fun j ↦ (W b).ι.appTop (c j)) (v b) (hv b)
  have localRule {T : Scheme.{u}} (b : I) (l : T ⟶ (W b).toScheme) (s : I → Γ(T, ⊤))
      (hs : Ideal.span (Set.range s) = ⊤) (eq : (l ≫ (W b).ι) ≫ y =
        homOfSections ((l ≫ (W b).ι) ≫ g) s hs) :
      l ≫ F b = reflectedHom ((l ≫ (W b).ι) ≫ g) a
        (fun j ↦ (l ≫ (W b).ι).appTop (c j)) s hs := by
    dsimp only [F]
    rw [comp_reflectedHom, Category.assoc, Scheme.Hom.comp_appTop]
    apply reflectedHom_congr
    simpa only [Category.assoc, eqv, comp_homOfSections] using eq
  have compat (b d : I) :
      X.homOfLE (inf_le_left : W b ⊓ W d ≤ W b) ≫ F b =
      X.homOfLE (inf_le_right : W b ⊓ W d ≤ W d) ≫ F d := by
    let l := X.homOfLE (inf_le_left : W b ⊓ W d ≤ W b)
    let r := X.homOfLE (inf_le_right : W b ⊓ W d ≤ W d)
    have e : l ≫ (W b).ι = r ≫ (W d).ι := by simp [l, r]
    have hr := span_range_appTop_eq_top r (hv d)
    rw [localRule b l _ hr (by
      rw [e, Category.assoc, eqv d, comp_homOfSections, Category.assoc]), e]
    simp only [F, comp_reflectedHom, Category.assoc, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, r]
  let z := Scheme.Opens.glueMorphismsOfTop W cover F compat
  have loc (b : I) : (W b).ι ≫ z = F b := Scheme.Opens.ι_glueMorphismsOfTop ..
  refine ⟨z, Scheme.Opens.hom_ext_of_iSup_eq_top W cover _ _ (fun b ↦ ?_), ?_⟩
  · rw [← Category.assoc, loc]
    exact homOfSections_over ..
  intro T f s hs eq
  let V (b : I) := f ⁻¹ᵁ W b
  apply Scheme.Opens.hom_ext_of_iSup_eq_top V (f.iSup_preimage_eq_top cover)
  intro b
  let l := f ∣_ W b
  have square : l ≫ (W b).ι = (V b).ι ≫ f := morphismRestrict_ι ..
  have et : (l ≫ (W b).ι) ≫ y = homOfSections ((l ≫ (W b).ι) ≫ g)
      (fun j ↦ (V b).ι.appTop (s j)) (span_range_appTop_eq_top _ hs) := by
    rw [square, Category.assoc, eq, comp_homOfSections, Category.assoc]
  rw [← Category.assoc, ← square, Category.assoc, loc, localRule _ _ _ _ et, square,
    comp_reflectedHom, Category.assoc, Scheme.Hom.comp_appTop]
  rfl


/-- A relative projective reflection fixes the base and takes the chosen coordinate
to the old coordinate plus the indicated linear combination of the other coordinates.
It negates the remaining coordinates. This formula applies to every tuple of sections
on every test scheme over the product. -/
public theorem exists_projectiveCoordinateReflection {I : Type u} [Fintype I] [DecidableEq I]
    {B S : Scheme.{u}} [IsAffine S] (d : B ⟶ S) (a : I) (c : I → Γ(B, ⊤)) :
    let π := ℙ(I; S) ↘ S
    let D := pullback d π
    let p := pullback.fst d π
    let q := pullback.snd d π
    ∃ σ : D ≅ D, σ.hom ≫ p = p ∧
      ∀ {T : Scheme.{u}} (f : T ⟶ D) (s : I → Γ(T, ⊤)) (hs : Ideal.span (Set.range s) = ⊤),
        f ≫ q = homOfSections (f ≫ q ≫ π) s hs →
        f ≫ σ.hom ≫ q = homOfSections (f ≫ q ≫ π)
          (chartReflection a (fun j ↦ (f ≫ p).appTop (c j)) s)
          (chartReflection_span _ _ _ hs) := by
  intro π D p q
  obtain ⟨z, hz, hzT⟩ := exists_reflectedHom a q (fun j ↦ p.appTop (c j))
  change z ≫ π = q ≫ π at hz
  let m : D ⟶ D := pullback.lift p z (pullback.condition.trans hz.symm)
  have mp : m ≫ p = p := pullback.lift_fst ..
  have mq : m ≫ q = z := pullback.lift_snd ..
  have rule {T : Scheme.{u}} (f : T ⟶ D) (s : I → Γ(T, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
      (eq : f ≫ q = homOfSections (f ≫ q ≫ π) s hs) :
      f ≫ m ≫ q = reflectedHom (f ≫ q ≫ π) a (fun j ↦ (f ≫ p).appTop (c j)) s hs := by
    rw [mq]
    exact hzT f s hs eq
  have mm : m ≫ m = 𝟙 D := by
    apply pullback.hom_ext
    · change (m ≫ m) ≫ p = 𝟙 D ≫ p
      simp only [Category.assoc, mp, Category.id_comp]
    · change (m ≫ m) ≫ q = 𝟙 D ≫ q
      rw [Category.id_comp]
      let W (b : I) := q ⁻¹ᵁ standardOpen I S b
      apply Scheme.Opens.hom_ext_of_iSup_eq_top W (q.iSup_preimage_eq_top (iSup_standardOpen I S))
      intro b
      let f := (W b).ι
      obtain ⟨hs, eq⟩ := homOfChartRatios (f ≫ q) b (fun x _ ↦ x.2)
      rw [Category.assoc] at eq
      have once := rule f _ hs eq
      let v (j : I) := (f ≫ p).appTop (c j)
      have hg : (f ≫ m) ≫ q ≫ π = f ≫ q ≫ π := by
        simp only [Category.assoc, ← Category.assoc m q, mq, hz]
      have eq' : (f ≫ m) ≫ q = homOfSections ((f ≫ m) ≫ q ≫ π) _ (chartReflection_span a v _ hs) := by
        rw [hg, Category.assoc]
        exact once
      have twice := rule (f ≫ m) _ _ eq'
      rw [hg, Category.assoc f m p, mp] at twice
      change (f ≫ m) ≫ m ≫ q = homOfSections _ (chartReflection a v (chartReflection a v _)) _ at twice
      simpa only [reflect_twice, Category.assoc] using twice.trans (by simpa only [reflect_twice] using eq.symm)
  exact ⟨⟨m, m, mm, mm⟩, mp, rule⟩

end WeilII


