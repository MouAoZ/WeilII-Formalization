module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial

/-! # Principal opens in a normalized hyperplane parameter chart -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace

universe u v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the dual space of Katz, Appendix A.1, a dense open contains a principal open in any
standard parameter chart. The specified bijection orders its affine coordinates. Pull the
open back to the polynomial spectrum, choose a basic open about one of its points, and
evaluate the polynomial at each normalized tuple to test membership. -/
public theorem exists_basicOpen_normalizedProjectiveParameters
    (K : Type u) [Field K] (J : Type u) (d : J) {ι : Type v} (e : {j : J // j ≠ d} ≃ ι)
    (W : ℙ(J; Spec (.of K)).Opens) (hW : Dense (W : Set ℙ(J; Spec (.of K)))) :
    let S := Spec (.of K)
    ∃ g : MvPolynomial ι K, g ≠ 0 ∧ ∀ (x : ι → K) (_ : MvPolynomial.eval x g ≠ 0),
      ∃ (H : S ⟶ ℙ(J; S)), H ≫ ℙ(J; S) ↘ S = 𝟙 S ∧ H (IsLocalRing.closedPoint K) ∈ W ∧
        ∃ hD : ⊤ ≤ H ⁻¹ᵁ standardOpen J S d,
          ∀ j : {j : J // j ≠ d}, H.appLE _ ⊤ hD (coordRatio J S d j) =
            (Scheme.ΓSpecIso (.of K)).inv (x (e j)) := by
  classical
  intro S
  let I := {j : J // j ≠ d}
  let q := chartMap J K d
  have : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion
    ((AffineSpace.SpecIso I (.of K)).inv ≫ (standardOpenIso J S d).inv ≫ (standardOpen J S d).ι))
  let U := q ⁻¹ᵁ W
  have dense : Dense (U : Set (Spec (.of (MvPolynomial {j : J // j ≠ d} K)))) := hW.preimage q.isOpenEmbedding.isOpenMap
  obtain ⟨y, hy⟩ := dense.nonempty
  obtain ⟨_, ⟨b, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen y hy
  have hb0 : b ≠ 0 := fun h ↦ (PrimeSpectrum.mem_basicOpen b y).mp hb (h ▸ y.asIdeal.zero_mem)
  refine ⟨MvPolynomial.rename e b, fun h ↦ hb0 ((MvPolynomial.rename_injective e e.injective)
    (h.trans (map_zero _).symm)), ?_⟩
  intro x hx
  let ev := MvPolynomial.eval (x ∘ e)
  let v := Spec.map (CommRingCat.ofHom ev)
  let H := v ≫ q
  have hbase : H ≫ ℙ(J; S) ↘ S = 𝟙 S := by
    simp only [H, S, q, chartMap, Category.assoc, standardOpenIso_inv_ι_over,
      AffineSpace.SpecIso_inv_over]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext z
    exact MvPolynomial.eval_C z
  have hD : ⊤ ≤ H ⁻¹ᵁ standardOpen J S d := v.preimage_mono (top_le_chartMap_preimage J K d)
  refine ⟨H, hbase, hsub ?_, hD, ?_⟩
  · change ev b ∉ IsLocalRing.maximalIdeal K
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    simpa only [MvPolynomial.eval_rename] using hx
  · intro j
    have h := chartToPoly_coordRatio J K d j
    apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
    change ((H.appLE (standardOpen J S d) ⊤ hD ≫ (Scheme.ΓSpecIso (.of K)).hom) _) = _
    rw [← Scheme.Hom.appLE_comp_appLE v q _ ⊤ ⊤ (top_le_chartMap_preimage J K d) le_top,
      Scheme.Hom.appLE_top_top, Category.assoc]
    change ((q.appLE _ ⊤ _ ≫ (Spec.map (CommRingCat.ofHom ev)).appTop ≫
      (Scheme.ΓSpecIso (.of K)).hom) _) = _
    rw [Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, CommRingCat.comp_apply]
    change ev (chartToPoly J K d (coordRatio J S d j)) = _
    rw [h, MvPolynomial.eval_X]
    exact ((Scheme.ΓSpecIso (.of K)).inv_hom_id_apply _).symm

end WeilII
