module

public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple

/-! # Affineness of the complement of a projective hyperplane -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace Scheme.Modules MonoidalCategory

universe u

/-- The complement of the incidence fiber at a field-valued hyperplane is affine
(Katz, Appendix A.5, p. 221). Normalize its coefficients on a chart containing the
parameter. On each standard chart of the point space the corresponding linear section
of the twisting line generates the same ideal as the incidence equation.
The coordinate sections of that line have affine nonvanishing loci covering projective
space. Properness over the field therefore makes the linear section's complement affine. -/
public theorem isAffineOpen_projectiveHyperplaneFiber_complement
    (K : Type u) [Field K] (I : Type u) [Fintype I]
    (H : Spec (CommRingCat.of K) ⟶ ℙ(I; Spec (CommRingCat.of K))) [H.IsOver (Spec (.of K))] :
    IsAffineOpen (projectiveHyperplaneFiber H).subschemeι.openComplement := by
  classical
  let S := Spec (CommRingCat.of K)
  let P := ℙ(I; S)
  let p := P ↘ S
  let U := standardOpen I S
  have covered (x : P) : ∃ a : I, x ∈ U a := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen I S).ge (Set.mem_univ x))
  obtain ⟨b, hb⟩ := covered (H (IsLocalRing.closedPoint K))
  have hbS : ⊤ ≤ H ⁻¹ᵁ U b := by
    intro x _
    change H x ∈ U b
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)]
  let w (i : I) := H.appLE (U b) ⊤ hbS (coordRatio I S b i)
  let M := twistRestrict (𝟙 P) 1
  let z (i : I) : Γ(M, ⊤) := pullbackSection (𝟙 P) (twistOneSection I S i)
  let lam : Γ(M, ⊤) := ∑ i : I, p.appTop (w i) • z i
  let φ := homOfGlobalSection M lam
  have hM := IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (unit P) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ P.Modules)
  let coverSection (i : I) : 𝟙_ P.Modules ⟶ M :=
    (pullbackObjUnitIso (𝟙 P)).inv ≫ (pullback (𝟙 P)).map (coordinateSection I S i)
  have chart (i : I) : (Hom.zeroLocus (coverSection i)).support.compl = U i := by
    exact (compl_support_zeroLocus_pullback (𝟙 P) (coordinateSection I S i)).trans
      (congrArg (fun V ↦ (𝟙 P) ⁻¹ᵁ V) (compl_support_zeroLocus_coordinateSection I S i))
  have haff := isAffineOpen_compl_support_zeroLocus p M coverSection
    (fun i ↦ (chart i) ▸ isAffineOpen_standardOpen I S i)
    (by simp_rw [chart]; exact iSup_standardOpen I S) φ
  have heq : (projectiveHyperplaneFiber H).subschemeι.openComplement = φ.zeroLocus.support.compl := by
    ext x
    obtain ⟨a, hxa⟩ := covered x
    let V : P.affineOpens := ⟨U a, isAffineOpen_standardOpen I S a⟩
    have frame : IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (z a)) :=
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 P) a
    have ratio (i : I) : M.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (z i) =
        coordRatio I S a i • M.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (z a) :=
      pullbackSection_twistOneSection_map_eq_smul (𝟙 P) i a
    have eqn : φ.app (U a) (1 : Γ(P, U a)) =
        (∑ i : I, P.presheaf.map (homOfLE (le_refl (U a))).op (coordRatio I S a i) *
          p.appLE ⊤ (U a) le_top (w i)) •
          M.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (z a) := by
      rw [homOfGlobalSection_app_one]
      simp only [lam, map_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Scheme.Modules.map_smul, ratio i, mul_smul, Scheme.presheaf_map_id_apply]
      exact smul_comm _ _ _
    have ideals : (projectiveHyperplaneFiber H).ideal V = φ.zeroLocus.ideal V :=
      (projectiveHyperplaneFiber_ideal H a b hbS V le_rfl).trans
        (Hom.ideal_zeroLocus φ V (isFreeGenerator_one _) frame eqn).symm
    change x ∉ Set.range (projectiveHyperplaneFiber H).subschemeι ↔ x ∉ φ.zeroLocus.support
    rw [Scheme.IdealSheafData.range_subschemeι]
    change x ∉ (projectiveHyperplaneFiber H).support ↔ x ∉ φ.zeroLocus.support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := projectiveHyperplaneFiber H) (U := V) hxa,
      Scheme.IdealSheafData.mem_support_iff_of_mem (I := φ.zeroLocus) (U := V) hxa, ideals]
  exact heq ▸ haff

end WeilII
