module

public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
import WeilConjectures.CategoryTheory.WeilLiftAdjunction
import WeilII.CategoryTheory.RecollementMateIsIso
import WeilII.AlgebraicGeometry.WeilCondensedDirectImageCarrier

/-!
# Geometric Frobenius on the exceptional inverse image of a closed immersion

Zhang, §2, p. 2, uses the closed-support triangle before (†). The comparison here expresses
its Weil exceptional inverse image in the geometric condensed model. It uses the adjunctions
in `WeilSheaf/Localization` and `Derived/Condensed/CondensedClosedSupportAdjunction`.
-/

open CategoryTheory Endofunctor AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- The geometric carrier of the native closed exceptional inverse image is naturally
isomorphic to derived closed support. Under this comparison the Frobenius acts by the mate
of the closed direct-image exchange followed by the descent of the input complex.

For the closed-support triangle of Zhang, §2 before (†), write `d` and `v` for the closed
and open maps on the geometric fibre. For either map the derived Weil direct image commutes
with passage to condensed Weil sheaves by `rightDerivedLowerStarCompToCondensedIso`.
Forget this comparison and compose with `derivedForgetCommIso` and the carrier comparisons
`condensedForgetObjIso` at source and target. For the closed map this gives a natural
isomorphism κ from the carrier of the Weil direct image to the termwise geometric direct
image L of the carrier, since closed direct image is exact. The formula for the structure
map of the derived Weil direct image and equivariance of the carrier comparisons identify
its descent, through κ, with the geometric direct-image exchange followed by L of descent.

Use κ inverse to view the forgotten Weil counit as a map a from LQ to the carrier of M,
where Q is the carrier of the Weil exceptional inverse image. Its transpose θ under the
geometric closed-support adjunction is natural in M. The forgotten Weil support triangle
has first arrow a and third object a derived open direct image, by the direct-image
comparisons and exactness of forgetting and of the model equivalence. For every geometric
complex P on the closed part, open restriction annihilates LP. By the open adjunction,
maps from every shift of LP to the third object vanish. The triangle exact sequence and
full faithfulness of L therefore identify maps P → Q bijectively with maps LP → U(M)
by applying L and composing with a. Under adjunction this is postcomposition with θ,
so Yoneda gives its invertibility. The direct-image exchange has invertible mate since
both Frobenius functors are equivalences. By the counit formula for mates, the equivariance
of κ and naturality of descent for the Weil counit give the displayed square for θ. -/
public theorem closedUpperShriekGeometricFrobeniusComparison
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
    let j := i.openComplement.ι
    let hij := eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι
    let hi := comp_over i (Spec (.of k))
    let hj := comp_over j (Spec (.of k))
    let d := Scheme.Hom.geometricFiberMap i hi
    let v := Scheme.Hom.geometricFiberMap j hj
    let hdv := (Scheme.Hom.isCompl_range_geometricFiberMap i j hi hj hij).eq_compl
    let Λ := Profinite.padicAlgClRingObj ℓ
    letI := CondensedRing.closedSupport_lowerStarExact Λ d v hdv
    let adj := CondensedRing.closedSupportDerivedAdjunction Λ d v hdv
    let exchange := IsoAlgebra.derivedExactCommIso
      (CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso Λ i hi)
    let mate := Adjunction.rightAdjointExchange adj adj exchange
    let R := (CondensedRing.closedSupport Λ d v).rightDerivedFunctor
    let B := WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ) i j hij
    let E (V : Scheme.{u}) [V.Over (Spec (.of k))] :=
      (adicSheafDerivedEquivCondensedMod ℓ (V ↘ Spec (.of k)).geometricFiber).functor
    let U (V : Scheme.{u}) [V.Over (Spec (.of k))] :=
      WeilComplex.forget (k₀ := k) (l := ℓ) (X := V) ⋙ E V
    let σ (V : Scheme.{u}) [V.Over (Spec (.of k))] (N : WeilComplex k ℓ V) :=
      transportWeilDatum (E V)
        (IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ V)).symm
        ((IsoAlgebra.derivedStrIso (WeilSheaf.frobeniusPullback k ℓ V)).hom.app N.obj)
    IsIso mate ∧ ∃ θ : B ⋙ U Z ≅ U X ⋙ R, ∀ M : WeilComplex k ℓ X,
      IsWeilEquivariant (WeilComplex.condensedFrobenius k ℓ Z).mapDerivedCategory
        (σ Z (B.obj M)) (mate.app ((U X).obj M) ≫ R.map (σ X M)) (θ.hom.app M) := by
  classical
  let := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  intro j hij hi hj d v hdv Λ adj exchange mate R B E U σ
  have : IsClosedImmersion d := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
    (P := @IsClosedImmersion) i hi inferInstance
  have : IsOpenImmersion v := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
    (P := @IsOpenImmersion) j hj inferInstance
  have : QuasiCompact v := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
    (P := @QuasiCompact) j hj inferInstance
  let := CondensedRing.closedSupport_lowerStarExact Λ d v hdv
  let F (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :=
    (WeilComplex.condensedFrobenius k ℓ Y).mapDerivedCategory
  have (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : (F Y).IsEquivalence :=
    inferInstanceAs (WeilComplex.condensedFrobenius k ℓ Y).mapDerivedCategory.IsEquivalence
  refine ⟨(NatTrans.isIso_iff_isIso_app _).2 (fun M ↦
    Adjunction.isIso_rightAdjointExchange_app adj exchange M), ?_⟩
  let a := WeilComplex.closedUpperShriekAdjunction (k₀ := k) (l := ℓ) i j hij
  obtain ⟨κ, hκ⟩ := WeilCondensedCarrier.exists_exactDirectImageIso k ℓ i
  let t : B ⋙ U Z ⟶ U X ⋙ R := Adjunction.rightAdjointExchange a adj κ
  obtain ⟨_, hc, _, _, hz, _⟩ := CondensedRing.condensedSupportDerivedLocalization Λ d v hdv
  let c := CondensedRing.closedPullbackDerivedAdjunction Λ d
  have : IsIso c.counit := (NatTrans.isIso_iff_isIso_app _).2 hc
  have ff := c.fullyFaithfulROfIsIsoCounit
  have ht : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro M
    obtain ⟨w, hw, _⟩ := WeilComplex.existsUnique_distTriang_closedSupportTriangle i j hij M
    let T := WeilComplex.closedSupportTriangle i j hij M w
    have hI := (WeilComplex.forgetBoundedConstructibleAdic k ℓ X).map_distinguished T hw
    have hU := (ProEtale.DerivedCategory.boundedConstructibleAdic ℓ
      (X ↘ Spec (.of k)).geometricFiber).ι.map_distinguished _ hI
    have hT := (adicSheafDerivedEquivCondensedMod ℓ
      (X ↘ Spec (.of k)).geometricFiber).functor.map_distinguished _ hU
    let N := (WeilComplex.upperStar j).obj M
    let e := (WeilCondensedCarrier.rightDerivedDirectImageIso k ℓ j).app N
    apply isIso_rightAdjointExchange_app_of_supportTriangle a adj κ ff M hT
    intro P n
    have h := Pretriangulated.Recollement.subsingleton_hom_shift _ _
      (CondensedRing.closedSupportOpenDerivedAdjunction Λ v) hz P
      ((WeilCondensedCarrier.carrier k ℓ _).obj N) n
    exact @Equiv.subsingleton _ _ e.homToEquiv h
  refine ⟨asIso t, fun M ↦ ?_⟩
  apply isWeilEquivariant_rightWeilDatum_of_counitCompat (adjW := a) (adj₀ := adj) hκ M ((asIso t).app M)
  change κ.hom.app (B.obj M) ≫ _ ≫ _ = _
  exact Adjunction.hom_app_comp_map_rightAdjointExchange_app_comp_counit a adj κ M

end WeilII
