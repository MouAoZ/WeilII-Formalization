module

public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # The complement of a normalized fiber of projective incidence -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace Scheme.Modules MonoidalCategory

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- When a parameter lies in the chart at `d`, the complement of its incidence fiber is
the nonvanishing locus of the section with the normalized coefficients (Katz A.1).
On each point-space chart at `a`, the section divided by the frame at `a` gives the sum
of the coordinate ratios times these coefficients. This generates the fiber ideal there.
The standard charts cover, so the complements agree everywhere. -/
public theorem normalizedHyperplaneFiber_openComplement
    {J : Type u} [Fintype J] {S : Scheme.{u}} [IsAffine S] (H : S ⟶ ℙ(J; S)) [H.IsOver S]
    (d : J) (hD : ⊤ ≤ H ⁻¹ᵁ standardOpen J S d) (l : J → Γ(S, ⊤))
    (hl : ∀ j, H.appLE _ ⊤ hD (coordRatio J S d j) = l j) :
    let P := ℙ(J; S)
    let lam := ∑ j, (P ↘ S).appTop (l j) • twistOneSection J S j
    (projectiveHyperplaneFiber H).subschemeι.openComplement =
      (homOfGlobalSection _ lam).zeroLocus.subschemeι.openComplement := by
  classical
  intro P lam
  let π := P ↘ S
  let L := twist J S 1
  let φ := homOfGlobalSection L lam
  let M := twistRestrict (𝟙 P) 1
  let z (j : J) : Γ(M, ⊤) := pullbackSection (𝟙 P) (twistOneSection J S j)
  let ψ := (pullbackObjUnitIso (𝟙 P)).inv ≫ (pullback (𝟙 P)).map φ
  have := IsInvertible.sheafOfModules_isInvertible L
  have := IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (unit P) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ P.Modules)
  have hφ : φ.app ⊤ (1 : Γ(P, ⊤)) = lam := by
    simp only [φ, homOfGlobalSection_app_one, presheaf_map_id_apply]
  have topEq : ψ.app ⊤ (1 : Γ(P, ⊤)) = ∑ j, π.appTop (l j) • z j := by
    rw [show ψ.app ⊤ (1 : Γ(P, ⊤)) = _ from (pullbackSection_app_one (𝟙 P) φ).symm, hφ]
    change ((pullbackPushforwardAdjunction (𝟙 P)).unit.app L).app ⊤ (∑ _, _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ pullbackSection_smul _ _ _
  have compare : (projectiveHyperplaneFiber H).support.compl = ψ.zeroLocus.support.compl := by
    ext x
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp ((iSup_standardOpen J S).ge
      (Set.mem_univ x))
    let U : P.affineOpens := ⟨standardOpen J S a, isAffineOpen_standardOpen _ _ _⟩
    let res := M.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
    have frame : IsFreeGenerator (res (z a)) := isFreeGenerator_pullbackSection_twistOneSection _ _
    have ratio (j : J) : res (z j) = coordRatio J S a j • res (z a) :=
      pullbackSection_twistOneSection_map_eq_smul (𝟙 P) j a
    have eqn : ψ.app U.1 (1 : Γ(P, U.1)) =
        (∑ j, P.presheaf.map (homOfLE (le_refl U.1)).op (coordRatio J S a j) *
          π.appLE ⊤ U.1 le_top (l j)) • res (z a) := by
      have eqRes := Hom.app_presheaf_map ψ (homOfLE (le_top : U.1 ≤ ⊤)) (1 : Γ(P, ⊤))
      rw [topEq] at eqRes
      change ψ.app U.1 (P.presheaf.map _ 1) = res _ at eqRes
      rw [map_one] at eqRes
      rw [eqRes]
      rw [map_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [res]
      rw [Scheme.Modules.map_smul, ratio j, mul_smul, Scheme.presheaf_map_id_apply]
      exact smul_comm _ _ _
    have ideals := projectiveHyperplaneFiber_ideal H a d hD U le_rfl
    simp_rw [hl] at ideals
    have eqIdeal := ideals.trans (Hom.ideal_zeroLocus ψ U (isFreeGenerator_one _) frame eqn).symm
    change x ∉ (projectiveHyperplaneFiber H).support ↔ x ∉ ψ.zeroLocus.support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := projectiveHyperplaneFiber H)
      (U := U) ha, Scheme.IdealSheafData.mem_support_iff_of_mem (I := ψ.zeroLocus) (U := U) ha,
      eqIdeal]
  have eqSupport := compare.trans (compl_support_zeroLocus_pullback (𝟙 P) φ)
  ext x
  change x ∉ Set.range _ ↔ x ∉ Set.range _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι]
  exact SetLike.ext_iff.mp eqSupport x

end WeilII
