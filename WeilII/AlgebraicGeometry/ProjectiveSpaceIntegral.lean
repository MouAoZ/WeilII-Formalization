module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace CategoryTheory

universe u

/-- Projective space over a field is integral. The standard charts are spectra of
polynomial domains, hence reduced and irreducible. Each meets a fixed chart in a
nonempty open (all coordinates can be chosen to be one), so that chart is dense.

This supplies the integral parameter space used for generic base change in Katz,
Appendix A.3, p. 220. -/
public theorem isIntegral_projectiveSpace_over_field (I k : Type u) [Nonempty I] [Field k] :
    IsIntegral ℙ(I; Spec (.of k)) := by
  classical
  let S := Spec (.of k)
  let P := ℙ(I; S)
  let U := standardOpen I S
  let i₀ : I := Classical.choice inferInstance
  let chart (i : I) := standardOpenIso I S i ≪≫ AffineSpace.SpecIso _ (.of k)
  have red (i : I) : IsReduced (U i).toScheme := isReduced_of_isOpenImmersion (chart i).hom
  have irr (i : I) : IsIrreducible (U i : Set P) := by
    have he := (chart i).inv.homeomorph.irreducibleSpace_iff.mp inferInstance
    exact isIrreducible_iff_irreducibleSpace.mpr he
  have hs : Ideal.span (Set.range (fun _ : I ↦ (1 : Γ(S, ⊤)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩) isUnit_one
  let x : P := homOfSections (𝟙 S) _ hs (IsLocalRing.closedPoint k)
  have hx (i : I) : x ∈ U i := by
    change IsLocalRing.closedPoint k ∈ homOfSections (𝟙 S) _ hs ⁻¹ᵁ standardOpen I S i
    rw [homOfSections_preimage_standardOpen, Scheme.basicOpen_of_isUnit _ isUnit_one]
    trivial
  have cov : TopologicalSpace.IsOpenCover U := iSup_standardOpen I S
  have denseChart : Dense (U i₀ : Set P) := by
    intro y
    have hy : y ∈ ⨆ i, U i := cov.symm ▸ (show y ∈ (⊤ : P.Opens) by trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen (irr i).2 (U i₀).isOpen
        ⟨x, hx i, hx i₀⟩ hi)
  refine (isIntegral_iff_irreducibleSpace_and_isReduced P).2 ⟨?_, ?_⟩
  · apply (irreducibleSpace_def P).2
    change IsIrreducible (Set.univ : Set P)
    rw [← denseChart.closure_eq]
    exact (irr i₀).closure
  · exact (IsReduced.iff_of_openCover P (P.openCoverOfIsOpenCover U cov)).2 red

end WeilII
