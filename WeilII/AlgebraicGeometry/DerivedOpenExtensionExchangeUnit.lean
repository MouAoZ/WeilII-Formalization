module

public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilII.AlgebraicGeometry.DerivedOpenExtensionUnitEquation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
public import WeilII.CategoryTheory.TransportExchangeUnit

/-!
# The open-extension unit on the ambient derived category

The exchange used in `WeilConjectures.WeilSheaf.CondensedModelBaseChange` comes from the
sheaf-level exchange by levelwise derivation. We compare it with the total derived pullbacks.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

/-- For a cartesian square of open immersions of schemes, the inverse open exchange
transposes to pullback of the unit followed by the ambient pullback square. On sheaves,
the inverse exchange is the left mate by
`purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv`. Its unit identity derives
levelwise by `mapDerivedCategoryAdjunction_mate`. Identify each total derived pullback with
its levelwise version. The pullback square comparison in these coordinates is the levelwise
square by `leftDerivedFunctorSquareIso_hom_app`, so transporting the unit equation gives
the stated component. -/
public theorem derivedOpenExtensionExchangeUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U Z U' Z' : Scheme.{u}} {j : U ⟶ Z} {j' : U' ⟶ Z'} [IsOpenImmersion j] [IsOpenImmersion j']
    {p : U' ⟶ U} {q : Z' ⟶ Z} (sq : IsPullback p j' j q)
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    let cp := leftDerivedUpperStarIsoMapDerivedCategory Λ p
    let cq := leftDerivedUpperStarIsoMapDerivedCategory Λ q
    let E := openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq.flip
    DerivedOpenExtensionUnitEquation Λ sq.toCommSq K
      (D((j')_!open⟦Λ⟧).map (cp.hom.app K) ≫ E.inv.app K ≫
          cq.inv.app (D((j)_!open⟦Λ⟧).obj K)) := by
  dsimp only [DerivedOpenExtensionUnitEquation]
  have := CachedModInstances.cached_hasTensor₄ObjExt Λ
  have := CachedModInstances.cached_hasGoodTensor₁₂Tensor Λ
  have := CachedModInstances.cached_hasGoodTensorTensor₂₃ Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorLeft Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorRight Λ
  have := CachedModInstances.cached_hasFunctorialFlatResolution Λ
  let θ := upperStarSquareComparison Λ sq.flip.toCommSq
  let e := openImmersionLowerShriekUpperStarBaseChangeIso Λ sq.flip
  refine transportExchangeUnit _ _ _ _ _ _ K _ ((Functor.mapDerivedCategorySquareIso θ).hom.app _)
    _ ?_ ?_
  · have h := Adjunction.mapDerivedCategoryAdjunction_mate
      (openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openImmersionLowerShriekUpperStarAdjunction Λ j') θ e.symm (fun A ↦ by
        dsimp only [e, Iso.symm_hom]
        rw [purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv]
        exact Adjunction.unit_app_comp_map_exchangeLeft_app _ _ _ _) K
    rw [Functor.mapDerivedCategorySquareIso_symm] at h
    exact h
  · rw [pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
    exact Adjunction.leftDerivedFunctorSquareIso_hom_app θ _

end WeilII

