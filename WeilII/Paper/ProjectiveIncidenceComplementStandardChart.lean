module

public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilII.AlgebraicGeometry.ProjectiveChartRatiosPresentation
import WeilII.AlgebraicGeometry.ProjectiveCoordinateReflection
import WeilII.AlgebraicGeometry.RelativeOpenProductTrivialization

/-!
# The universal hyperplane complement on a standard chart

Katz, *Affine cohomological transforms*, Appendix A.1, p. 218, trivializes the inclusion
of the incidence complement over each standard chart of the first projective space.
The square in A.2 uses the pullback of this trivialization along a map to that chart.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits ProjectiveSpace

universe u

/-- Katz, Appendix A.1, p. 218. In a basis and its dual, the two projective spaces have
the same coordinate index type. Write `U` for the standard chart at `a` in either factor.
Over the first chart, `σ` identifies the incidence complement inclusion with
`i : U × U ⟶ U × P∨`. For every `h : T ⟶ U`, the ambient and open isomorphisms commute
with the product maps induced by `h`. All products are over the given field.

Proof. On the first chart put xᵢ = Xᵢ/Xₐ. Replace Yₐ by Yₐ + ∑ᵢ≠ₐ xᵢYᵢ, fixing all
other dual coordinates. On the dual chart at b, apply the formula to the tuple Yᵢ/Y_b.
The transformed entries generate the unit ideal since subtracting the same sum recovers
the old tuple, whose b-th entry is one. On overlaps, changing b rescales the whole tuple
by a unit, so the maps to projective space agree. Pair the glued map with the first projection.
The subtraction formula gives its inverse. Indeed, on a chart where a transformed entry
z_d is invertible, the second substitution acts on zᵢ/z_d and recovers the original tuple
scaled by 1/z_d. Such charts cover, and the same calculation applies in the opposite order.

The inverse image of the target dual chart is the basic open of the transformed a-th
entry. On the input chart at b this entry is ∑ᵢ (Xᵢ/Xₐ)(Yᵢ/Y_b), the local generator
of the incidence ideal. Hence restricting the automorphism gives the required isomorphism
of opens over the ambient map. Pull both isomorphisms back along h. The coefficients become
h*(Xᵢ/Xₐ), so the ambient maps commute with h × id. Restricting this identity to the open
subschemes gives the last square by monicity of their inclusions. -/
public theorem projectiveIncidenceComplement_standardChart
    (k : Type u) [Field k] (I : Type u) [Fintype I] [Nontrivial I] (a : I) :
    let S := Spec (CommRingCat.of k)
    let π := ℙ(I; S) ↘ S
    let U := standardOpen I S a
    let u₀ := U.ι ≫ π
    let j := pullback.map u₀ π π π U.ι (𝟙 _) (𝟙 _) (by simp [u₀]) (by simp)
    let C := j ⁻¹ᵁ (projectiveHyperplaneIncidenceFamily I S).subschemeι.openComplement
    let i := pullback.map u₀ u₀ u₀ π (𝟙 _) U.ι (𝟙 _) (by simp) (by simp [u₀])
    ∃ (σ : pullback u₀ π ≅ pullback u₀ π) (e : C.toScheme ≅ pullback u₀ u₀),
      σ.hom ≫ pullback.fst u₀ π = pullback.fst u₀ π ∧
      e.hom ≫ i = C.ι ≫ σ.hom ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ U.toScheme),
        let t := h ≫ u₀
        let H := pullback.map t π u₀ π h (𝟙 _) (𝟙 _) (by simp [t]) (by simp)
        let Hopen := pullback.map t u₀ u₀ u₀ h (𝟙 _) (𝟙 _) (by simp [t]) (by simp)
        let iT := pullback.map t u₀ t π (𝟙 _) U.ι (𝟙 _) (by simp) (by simp [u₀])
        ∃ (σT : pullback t π ≅ pullback t π) (eT : (H ⁻¹ᵁ C).toScheme ≅ pullback t u₀),
          σT.hom ≫ pullback.fst t π = pullback.fst t π ∧
          σT.hom ≫ H = H ≫ σ.hom ∧
          eT.hom ≫ iT = (H ⁻¹ᵁ C).ι ≫ σT.hom ∧
          eT.hom ≫ Hopen = (H ∣_ C) ≫ e.hom := by
  classical
  intro S π U u₀ j C i
  let D := pullback u₀ π
  let p := pullback.fst u₀ π
  let q := pullback.snd u₀ π
  let A := projectiveHyperplaneIncidenceFamily I S
  have hU : ⊤ ≤ U.ι ⁻¹ᵁ U := fun z _ ↦ z.2
  let c (l : I) := U.ι.appLE U ⊤ hU (coordRatio I S a l)
  -- Negating the other dual coordinates makes the chart substitution its own inverse.
  obtain ⟨σ, hp, hσ⟩ := exists_projectiveCoordinateReflection u₀ a c
  have compare {T : Scheme.{u}} [IsAffine T] (f : T ⟶ D) (b : I)
      (hb : ⊤ ≤ (f ≫ q) ⁻¹ᵁ standardOpen I S b) :
      f ⁻¹ᵁ C = f ⁻¹ᵁ (σ.hom ⁻¹ᵁ (q ⁻¹ᵁ U)) := by
    let x := (f ≫ p) ≫ U.ι
    let y := f ≫ q
    have ha : ⊤ ≤ x ⁻¹ᵁ U := fun z _ ↦ ((f ≫ p) z).2
    let r (l : I) := x.appLE U ⊤ ha (coordRatio I S a l)
    let s (l : I) := y.appLE _ ⊤ hb (coordRatio I S b l)
    have coeff (l : I) : (f ≫ p).appTop (c l) = r l := by
      dsimp only [c, r, x]
      rw [← Scheme.Hom.appLE_top_top (f ≫ p) le_top, ← CommRingCat.comp_apply]
      exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE (f ≫ p) U.ι U ⊤ ⊤ hU le_top) _
    have ra : r a = 1 := by simp [r]
    let eqn := ∑ l : I, r l * s l
    have value : chartReflection a (fun l ↦ (f ≫ p).appTop (c l)) s a = eqn := by
      simp only [chartReflection, ↓reduceIte, coeff]
      simpa only [ra, one_mul] using
        Finset.add_sum_erase Finset.univ (fun l ↦ r l * s l) (Finset.mem_univ a)
    obtain ⟨hs, ey⟩ := homOfChartRatios y b hb
    have hy : f ≫ q = homOfSections (f ≫ q ≫ π) s hs := by simpa only [y, Category.assoc] using ey
    have transformed : (f ≫ σ.hom ≫ q) ⁻¹ᵁ U = T.basicOpen eqn := by
      rw [hσ f _ hs hy, homOfSections_preimage_standardOpen, value]
    have over : x ≫ π = y ≫ π := by
      change ((f ≫ p) ≫ U.ι) ≫ π = (f ≫ q) ≫ π
      simp only [Category.assoc]
      exact congrArg (f ≫ ·) (pullback.condition (f := u₀) (g := π))
    have pair : f ≫ j = pullback.lift x y over := by
      apply pullback.hom_ext <;> simp [j, x, y, p, q]
    let V : T.affineOpens := ⟨⊤, isAffineOpen_top T⟩
    have ideal : (A.comap (f ≫ j)).ideal V = Ideal.span {eqn} := by
      rw [pair]
      exact projectiveHyperplaneIncidenceFamily_ideal x y over a b V ha hb
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage σ.hom,
      ← Scheme.Hom.comp_preimage f, transformed]
    ext z
    change (f ≫ j) z ∉ Set.range A.subschemeι ↔ z ∈ T.basicOpen eqn
    rw [Scheme.IdealSheafData.range_subschemeι]
    have hsupp : (f ≫ j) z ∈ A.support ↔ z ∈ (A.comap (f ≫ j)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    change (f ≫ j) z ∉ A.support ↔ _
    rw [hsupp, Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) (show z ∈ V.1 from trivial),
      ideal, T.zeroLocus_span, T.zeroLocus_singleton]
    exact not_not
  have hc : C = σ.hom ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    ext z
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen I S).ge (Set.mem_univ (q z)))
    obtain ⟨_, ⟨V : D.Opens, hV, rfl⟩, hz, hsub⟩ := D.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ q ⁻¹ᵁ standardOpen I S b from hb) (q ⁻¹ᵁ standardOpen I S b).isOpen
    have : IsAffine V.toScheme := hV
    exact SetLike.ext_iff.mp (compare V.ι b (fun w _ ↦ hsub w.2)) ⟨z, hz⟩
  obtain ⟨e, he, hbase⟩ := relativeOpenProductTrivialization u₀ π U σ hp C hc
  exact ⟨σ, e, hp, he, hbase⟩

end WeilII




