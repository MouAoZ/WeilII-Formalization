module

public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.Tensor
import WeilConjectures.WeilSheaf.CohomologyShift
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.WeilSheaf.LowerShriekPackage
import WeilII.Paper.SmoothDivisorRelativePurity
import WeilII.Paper.SmoothDivisorRelativePurityLowDimension

/-!
# The compactly supported Gysin sequence for a smooth affine hypersurface

Zhang, *On an elementary proof of Weil II*, §2, p. 2, obtains (†) from the localization
triangle and relative purity for a smooth hypersurface.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The Frobenius-equivariant long exact sequence underlying Zhang's (†), p. 2. In degree
`r`, the Gysin map goes from the degree `r-2` group of `i^*G(-1)` to the degree `r` group of
`G`. The next map is induced by the open restriction unit, and the boundary lands in degree
`r-1` on the hypersurface. All groups are geometric compactly supported cohomology.

Proof. Write `K = G[0]`. For the closed immersion i and its complementary open immersion j,
localization gives the distinguished triangle with first map the counit from `Ri_*Ri^!K` to
K and second map the unit from K to `Rj_*j^*K`. The open complement is quasi-compact since
affine space over k is noetherian. Pullback commutes with placement in degree zero, which
identifies the third term with `Rj_*((j^*G)[0])` and gives the displayed restriction map.

Relative purity for a smooth divisor with lisse coefficients identifies `Ri^!K` with
`(i^*G(-1))[−2]` as Weil complexes (SGA 4, Exposé XVI, 3.7, 3.8 and 3.10(a)). The closed
immersion is proper, so its ordinary and compactly supported direct images agree. Composing
the latter with the compactly supported direct image to the base therefore identifies the
degree-r group of the first term with the degree-(r−2) group on the hypersurface.

Apply compactly supported cohomology to the triangle. Its two induced maps and its boundary
commute with Frobenius and are exact at all three successive terms. Transport the maps by
the above Weil isomorphisms in every degree. These preserve images, kernels and Frobenius,
and the next closed term has degree (r+1)−2 = r−1. -/
public theorem smoothHypersurfaceGysinSequence
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {n : ℕ} {Y : Scheme.{u}}
    (i : Y ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) [IsSmoothAffineHypersurface i]
    (G : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) (hG : G.IsLisse) :
    let a := 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)
    letI : Y.Over (Spec (CommRingCat.of k)) := ⟨i ≫ a⟩
    letI : i.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
    letI : IsSeparated (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsSeparated (i ≫ a))
    letI : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (i ≫ a))
    letI : QuasiCompact (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (QuasiCompact (i ≫ a))
    letI := isNoetherian_of_locallyOfFiniteType a
    let L := ((WeilSheaf.upperStar i).obj G).tensorObj (WeilSheaf.tateTwistSheaf k ℓ Y (-1))
      (hG.upperStar i)
    let j := i.openComplement.ι
    let D := openImmersionDerivedDirectImageOfRestriction j G
    let η : WeilSheaf.toComplex.obj G ⟶ D :=
      (WeilComplex.upperStarDerivedLowerStarAdjunction (k₀ := k) (l := ℓ) j).homEquiv
        (WeilSheaf.toComplex.obj G) (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar j).obj G))
        ((WeilSheaf.toComplexCompUpperStarIso (k₀ := k) (l := ℓ) j).hom.app G)
    let A := fun r : ℤ ↦ L.compactlySupportedCohomology (r - 2)
    let B := fun r : ℤ ↦ G.compactlySupportedCohomology r
    let C := fun r : ℤ ↦ D.compactlySupportedCohomology r
    let res := WeilComplex.compactlySupportedCohomologyMap η
    ∃ (gysin : ∀ r, (A r).carrier →ₗ[PadicAlgCl ℓ] (B r).carrier)
      (δ : ∀ r, (C r).carrier →ₗ[PadicAlgCl ℓ] (A (r + 1)).carrier), ∀ r : ℤ,
      Function.Exact (gysin r) (res r) ∧
      Function.Exact (res r) (δ r) ∧
      Function.Exact (δ r) (gysin (r + 1)) ∧
      Function.Semiconj (gysin r) (A r).frobenius (B r).frobenius ∧
      Function.Semiconj (res r) (B r).frobenius (C r).frobenius ∧
      Function.Semiconj (δ r) (C r).frobenius (A (r + 1)).frobenius := open Pretriangulated in by
  classical
  intro a L j D η A B C res
  letI : Y.Over (Spec (CommRingCat.of k)) := ⟨i ≫ a⟩
  letI : i.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  letI : IsSeparated (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsSeparated (i ≫ a))
  letI : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (i ≫ a))
  letI : QuasiCompact (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (QuasiCompact (i ≫ a))
  letI := isNoetherian_of_locallyOfFiniteType a
  let K := WeilSheaf.toComplex.obj G
  have hij : IsCompl (Set.range i.base) (Set.range j.base) :=
    eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι
  let M := (WeilComplex.closedUpperShriek i j hij).obj K
  have purity : Nonempty (M ≅ (WeilSheaf.toComplex.obj L)⟦(-2 : ℤ)⟧) := by
    by_cases hn : 2 ≤ n
    · obtain ⟨e, _⟩ := smoothDivisorRelativePurity (ℓ := ℓ) (by simpa using hn) i
      exact ⟨e G hG⟩
    · exact smoothDivisorRelativePurityLowDimension (by simpa using Nat.lt_of_not_ge hn) i G hG
  obtain ⟨ePur⟩ := purity
  obtain ⟨w, hw, _⟩ := WeilComplex.existsUnique_distTriang_closedSupportTriangle i j hij K
  let T := WeilComplex.closedSupportTriangle i j hij K w
  let α : T.obj₃ ≅ D := (WeilComplex.derivedLowerStar (k₀ := k) (l := ℓ) j).mapIso
    ((WeilSheaf.toComplexCompUpperStarIso (k₀ := k) (l := ℓ) j).app G)
  let T' := Triangle.mk T.mor₁ η (α.inv ≫ w)
  have hη : T.mor₂ ≫ α.hom = η := rfl
  have hT' : T' ∈ distTriang _ := by
    apply isomorphic_distinguished T hw T'
    apply (Triangle.isoMk T T' (Iso.refl _) (Iso.refl _) α ?_ ?_ ?_).symm
    · change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
      simp only [Category.comp_id, Category.id_comp]
    · change T.mor₂ ≫ α.hom = 𝟙 _ ≫ η
      simpa only [Category.id_comp] using hη
    · change w ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = α.hom ≫ α.inv ≫ w
      exact (congrArg (w ≫ ·) ((shiftFunctor _ (1 : ℤ)).map_id _)).trans
        ((Category.comp_id w).trans (α.hom_inv_id_assoc w).symm)
  obtain ⟨eComp⟩ := WeilComplex.nonempty_derivedLowerShriekCompIso
    (k₀ := k) (l := ℓ) i a (Y ↘ Spec (CommRingCat.of k)) rfl
  let eBase := (WeilComplex.derivedLowerShriek k ℓ a).mapIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar i M).symm ≪≫
    (eComp.app M).symm ≪≫
    (WeilComplex.derivedLowerShriek k ℓ (Y ↘ Spec (CommRingCat.of k))).mapIso ePur
  let e (r : ℤ) : (T'.obj₁.compactlySupportedCohomology r).Equiv (A r) :=
    (WeilComplex.cohomologyEquivOfIso eBase r).trans
      (WeilComplex.compactlySupportedCohomologyShiftEquiv (WeilSheaf.toComplex.obj L)
        (-2) r (r - 2) (by omega))
  let f (r : ℤ) := WeilComplex.compactlySupportedCohomologyMap T'.mor₁ r
  let b (r : ℤ) := WeilComplex.compactlySupportedCohomologyδ T' r (r + 1) rfl
  refine ⟨fun r ↦ (f r).comp (e r).toLinearEquiv.symm.toLinearMap,
    fun r ↦ (e (r + 1)).toLinearEquiv.toLinearMap.comp (b r), fun r ↦ ?_⟩
  refine ⟨?_, ?_, ?_, ?_, WeilComplex.compactlySupportedCohomologyMap_frobenius η r, ?_⟩
  · intro y
    refine (WeilComplex.exact_compactlySupportedCohomologyMap T' r hT' y).trans ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(e r).toLinearEquiv x, congrArg (f r) ((e r).toLinearEquiv.symm_apply_apply x)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(e r).toLinearEquiv.symm x, rfl⟩
  · intro y
    change (e (r + 1)).toLinearEquiv (b r y) = 0 ↔ _
    rw [map_eq_zero_iff _ (e (r + 1)).toLinearEquiv.injective]
    exact WeilComplex.exact_compactlySupportedCohomologyδ_left T' r (r + 1) rfl hT' y
  · intro y
    change f (r + 1) ((e (r + 1)).toLinearEquiv.symm y) = 0 ↔ _
    have h := WeilComplex.exact_compactlySupportedCohomologyδ_right T' r (r + 1) rfl hT'
      ((e (r + 1)).toLinearEquiv.symm y)
    refine h.trans ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (congrArg (e (r + 1)).toLinearEquiv hx).trans
        ((e (r + 1)).toLinearEquiv.apply_symm_apply y)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, ((e (r + 1)).toLinearEquiv.symm_apply_apply (b r x)).symm⟩
  · intro x
    change f r ((e r).symm.toLinearEquiv ((A r).frobenius x)) = _
    rw [(e r).symm.map_frobenius]
    exact WeilComplex.compactlySupportedCohomologyMap_frobenius T'.mor₁ r _
  · intro x
    change (e (r + 1)).toLinearEquiv (b r ((C r).frobenius x)) = _
    rw [show b r ((C r).frobenius x) = _ from
      WeilComplex.compactlySupportedCohomologyδ_frobenius T' r (r + 1) rfl x]
    exact (e (r + 1)).map_frobenius _

end WeilII
