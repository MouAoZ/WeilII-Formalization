module

public import WeilII.AlgebraicGeometry.LisseDirectImageVerdierDuality
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.WeilSheaf.Dual
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.DimensionOfImageClosure
import WeilII.AlgebraicGeometry.GeometricAdicTateLineLisse
import WeilII.AlgebraicGeometry.QuasiFiniteShriekClosedSupport

/-! # Compactly supported cohomology of a quasi-finite direct image on an affine scheme -/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- For a quasi-finite map from a smooth source of relative dimension d to an affine
scheme, compactly supported cohomology of the direct image of a lisse sheaf vanishes
below d. This is the affine vanishing step in Katz, Appendix A.5, pp. 220–221.
Duality turns the group into ordinary cohomology of the exceptional image of the
twisted dual in degree 2d−r. This exceptional image is represented on the closed image
by a constructible sheaf. The image closure has dimension at most d and is affine,
so the affine dimension bound applies. Linear duals detect zero. -/
public theorem isZero_compactCohomology_quasiFinite_lisse_of_affine
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {V B : Scheme.{u}} [IsAffine B] (a : B ⟶ Spec (CommRingCat.of (AlgebraicClosure k)))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] (g : V ⟶ B) [LocallyQuasiFinite g]
    (d : ℕ) [SmoothOfRelativeDimension d (g ≫ a)] [IsSeparated (g ≫ a)] [QuasiCompact (g ≫ a)]
    (M : ProEtale.AdicSheaf ℓ V) (hM : ProEtale.IsAdicLisseSheaf M) (r : ℤ) (hr : r < d) :
    IsZero ((ProEtale.algClosedCompactlySupportedCohomology ℓ a r).obj
      ((ProEtale.adicLowerStar ℓ g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  let S := Spec (CommRingCat.of (AlgebraicClosure k))
  have : Smooth (g ≫ a) := SmoothOfRelativeDimension.smooth d _
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g a
  have : QuasiCompact g := QuasiCompact.of_comp g a
  have : IsSeparated g := IsSeparated.of_comp g a
  let c := NagataCompactification g
  let T := (ProEtale.adicSheafEquivCondensedMod ℓ S).inverse.obj (ProEtale.tateTwist S ℓ (d : ℤ))
  let N := (ProEtale.AdicSheaf.ihom M).obj ((ProEtale.adicUpperStar ℓ (g ≫ a)).obj T)
  have hN : ProEtale.IsAdicConstructibleSheaf N :=
    (hM.ihom ((isAdicLisseSheaf_geometricTateLine k ℓ d).upperStar (g ≫ a))).isAdicConstructibleSheaf
  let C := TopologicalSpace.Closeds.closure (Set.range g)
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let i := J.subschemeι
  have hi : Set.range i = closure (Set.range g) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsAffine J.subscheme := isAffine_of_isAffineHom i
  have hdim : topologicalKrullDim J.subscheme ≤ d := by
    rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range, hi]
    exact (topologicalKrullDim_closure_range_le_source a g).trans
      (topologicalKrullDim_le_of_smoothOfRelativeDimension (g ≫ a) d)
  obtain ⟨A, hA, cmp⟩ := exists_constructible_cohomologyIso_of_quasiFinite_closedSupport
    k ℓ a g c N hN i (show Set.range g ⊆ Set.range i by rw [hi]; exact subset_closure)
  let m := 2 * (d : ℤ) - r
  obtain ⟨e⟩ := cmp m
  have hz := isZero_algClosedCohomology_of_isAffine k ℓ (i ≫ a) A hA d
    (lt_of_le_of_lt hdim (by norm_cast; omega)) m (by dsimp [m]; omega)
  have hzero := (WeilCoefficients.toModuleCat ℓ).map_isZero (hz.of_iso e)
  obtain ⟨D, _⟩ := exists_natural_lisseDirectImageVerdierDuality k ℓ a g d c r
  have hdual := (D M hM).toEquiv.subsingleton_congr.mpr (ModuleCat.subsingleton_of_isZero hzero)
  have hsub := (Module.subsingleton_dual_iff (PadicAlgCl ℓ)).mp hdual
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end WeilII
