module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicUpperStarKFlat
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # K-flatness of geometric pullback with a condensed coefficient

We apply the two K-flatness results used in WeilConjectures' `AdicUpperStarKFlat` directly to
the factorization of the condensed-ring inverse image in `ModuleObject.UpperLowerStar.Defs`.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
/-- Geometric pullback with coefficients pulled back from the point preserves K-flat
complexes. First apply the inverse image on the underlying module objects, which preserves
K-flatness by `preservesKFlatComplexes_mapMod_proEtale`. Its coefficient change is extension
along the isomorphism `condensedPullbackHom`; apply `kFlat_extendScalars_iff` to this factor.
Source: WeilConjectures' `ProEtaleInternalPullbackKFlat` and `AdicUpperStarKFlat`. -/
theorem condensedCoefficientPullback_preservesKFlat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
    {S T : Scheme.{u}} (f : S ⟶ T) :
    (CondensedRing.upperStar Λ f).PreservesKFlatComplexes := by
  constructor
  intro K hK
  let F := (ProEtale.upperStar Ab.{u+1} f).mapMod (condensedRingObj Λ T)
  let G := Mod.extendScalars (condensedPullbackHom Λ f)
  have hF := (CondensedRing.preservesKFlatComplexes_mapMod_proEtale f (condensedRingObj Λ T)).kFlat_map K hK
  have hG := (kFlat_extendScalars_iff (condensedPullbackHom Λ f)
    ((F.mapHomologicalComplex (.up ℤ)).obj K)).2 hF
  exact (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app K) hG

end WeilII
