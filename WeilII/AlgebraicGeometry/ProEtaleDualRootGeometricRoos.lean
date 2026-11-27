module

public import WeilII.AlgebraicGeometry.EtaleDualRootsOfUnityReductionTower
public import WeilII.CategoryTheory.SingleTowerRoosAugmentation
import WeilII.AlgebraicGeometry.EtaleDualRootsOfUnityReductionEpi
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationFree
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For the realized dual root tower on any scheme with ℓ invertible, the ordinary
limit in degree zero maps quasi-isomorphically to the strict Roos complex, with its
canonical projections. Exact adic extension preserves this map and gives vanishing
of every nonzero cohomology sheaf. This uses the epimorphic tower criterion, before
any choice of geometric roots or Frobenius descent. -/
public theorem proEtaleDualRootGeometricRoos
    (V : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hV : IsUnit (ℓ : Γ(V, ⊤))) :
    let D := etaleDualRootsOfUnityReductionTower V ℓ hV
    let T := D ⋙ (comparisonUpperStar Ab.{u + 1} V ⋙ Mod.free (padicIntAbSheaf V ℓ))
    let S := CochainComplex.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (padicIntAbSheaf V ℓ)) (0 : ℤ)
    let K := T ⋙ S
    let R := WeilConjectures.integralOperationsRoos K
    letI : (adicSheafExtendScalars V ℓ).IsLeftAdjoint :=
      (adicSheafExtendScalarsRestrictAdjunction V ℓ).isLeftAdjoint
    let E := (adicSheafExtendScalars V ℓ).mapHomologicalComplex (.up ℤ)
    ∀ c : Cone T, IsLimit c →
      (∃ ι : S.obj c.pt ⟶ R, QuasiIso ι ∧ QuasiIso (E.map ι) ∧
        HasRoosProjections (T := K) ι (fun n ↦ S.map (c.π.app (op n)))) ∧
        ∀ b : ℤ, b ≠ 0 → IsZero ((E.obj R).homology b) := by
  intro D T S K R E c hc
  have : (adicSheafExtendScalars V ℓ).IsLeftAdjoint :=
    (adicSheafExtendScalarsRestrictAdjunction V ℓ).isLeftAdjoint
  have ht (n : ℕ) : Epi (T.map (homOfLE n.le_succ).op) := by
    have : Epi (D.map (homOfLE n.le_succ).op) := etaleDualRootsOfUnityReductionEpi V ℓ hV n
    have : (Mod.free (padicIntAbSheaf V ℓ)).IsLeftAdjoint :=
      (Mod.freeForgetAdjunction (padicIntAbSheaf V ℓ)).isLeftAdjoint
    exact (comparisonUpperStar Ab.{u + 1} V ⋙ Mod.free (padicIntAbSheaf V ℓ)).map_epi _
  obtain ⟨ι, hι, hπ⟩ := singleTowerRoosAugmentation
    (Mod.epiπAppZeroOfEpi (R := padicIntAbSheaf V ℓ) (Scheme.ProEt.epi_π_app_zero_of_epi_ab (S := V)))
    T ht c hc
  have : IsIso (rationalizationComparison ℓ V) :=
    isIso_rationalizationComparison_of_regular ℓ V (isIso_rationalizationComparison_app_regular ℓ V)
  have := preservesFiniteLimits_adicSheafExtendScalars ℓ V
  have hι' : QuasiIso (E.map ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ι (adicSheafExtendScalars V ℓ)
  refine ⟨⟨ι, hι, hι', hπ⟩, fun b hb ↦ ?_⟩
  have transfer {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
      {L M : CochainComplex A ℤ} (f : L ⟶ M) (hf : QuasiIso f) (hL : IsZero (L.X b)) :
      IsZero (M.homology b) :=
    (isoOfQuasiIsoAt f b).isZero_iff.mp (ShortComplex.isZero_homology_of_isZero_X₂ (L.sc b) hL)
  exact transfer (A := AdicSheaf ℓ V) (L := E.obj (S.obj c.pt)) (M := E.obj R) (E.map ι) hι'
    ((adicSheafExtendScalars V ℓ).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 c.pt b hb))

end WeilII
