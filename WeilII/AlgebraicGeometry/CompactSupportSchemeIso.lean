module

public import WeilConjectures.WeilSheaf.Cohomology
import WeilConjectures.WeilSheaf.CohomologyShift
import WeilConjectures.WeilSheaf.LowerShriekPackage
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.UpperStarId

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- Pulling a Weil sheaf back along a scheme isomorphism preserves compactly supported
cohomology with Frobenius. This identifies affine-space coordinates in Zhang's change of
constants, §2. Compact-support base change along the square over the identity of the
base identifies the two direct images; take cohomology in degree r. -/
public theorem compactSupportEquiv_of_schemeIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (e : X ≅ Y) [e.hom.IsOver (Spec (CommRingCat.of k))] (F : WeilSheaf k ℓ Y) (r : ℤ) :
    Nonempty ((((WeilSheaf.upperStar e.hom).obj F).compactlySupportedCohomology r).Equiv
      (F.compactlySupportedCohomology r)) := by
  let S := Spec (CommRingCat.of k)
  have sq : IsPullback e.hom (X ↘ S) (Y ↘ S) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, comp_over]⟩
  let K := WeilSheaf.toComplex.obj F
  obtain ⟨bc⟩ := WeilComplex.nonempty_upperStarDerivedLowerShriekIso_of_isPullback sq K
  let unit := (WeilComplex.upperStarIdIso (k₀ := k) (l := ℓ) S).app
    ((WeilComplex.derivedLowerShriek k ℓ (Y ↘ S)).obj K)
  let pull := (WeilComplex.derivedLowerShriek k ℓ (X ↘ S)).mapIso
    ((WeilSheaf.toComplexCompUpperStarIso (k₀ := k) (l := ℓ) e.hom).app F)
  exact ⟨WeilComplex.cohomologyEquivOfIso (pull.symm ≪≫ bc.symm ≪≫ unit) r⟩

end WeilII
