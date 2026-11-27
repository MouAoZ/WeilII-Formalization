module

public import WeilII.AlgebraicGeometry.TateShiftDerivedLowerStar
public import WeilConjectures.WeilSheaf.VerdierDualLocalization
import WeilConjectures.WeilSheaf.LowerShriekPackage
import WeilConjectures.WeilSheaf.SmoothPurityAbsolute

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- For a closed pair smooth over the finite field of dimensions `d+1` and `d`,
the exceptional restriction of the constant Weil sheaf is the negative Tate line
shifted by `-2` (SGA 4, XVI, 3.8 and 3.10(a)). Composition of compactly supported
images and the two absolute smooth orientations identify the exceptional restriction
of the ambient dualizing complex with the dualizing complex of the closed scheme.
The direct image commutes with invertible Tate twists and shifts, so its right
adjoint also commutes with them. Cancel the ambient twist and shift. -/
public theorem smoothClosedConstantOrientation
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension (d+1) (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension d (Y ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (i : Y ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    letI := SmoothOfRelativeDimension.smooth (d+1) (X ↘ Spec (.of k))
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
    let S := WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ) i i.openComplement.ι
      (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
    Nonempty (S.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k ℓ X)) ≅
      (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k ℓ Y (-1)))⟦(-2 : ℤ)⟧) := by
  have := SmoothOfRelativeDimension.smooth (d+1) (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth d (Y ↘ Spec (.of k))
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  intro S
  let a := X ↘ Spec (.of k)
  let b := Y ↘ Spec (.of k)
  have : QuasiCompact b := by dsimp [b]; rw [← comp_over i (Spec (.of k))]; infer_instance
  have : IsSeparated b := by dsimp [b]; rw [← comp_over i (Spec (.of k))]; infer_instance
  let adj := WeilComplex.closedUpperShriekAdjunction (k₀ := k) (l := ℓ) i i.openComplement.ι
    (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
  let n : ℤ := d + 1
  let E (V : Scheme.{u}) [V.Over (Spec (.of k))] [LocallyOfFiniteType (V ↘ Spec (.of k))] :=
    WeilComplex.tateTwistShiftEquiv k ℓ V (-n) n (-(2*n)) (2*n) (neg_add_cancel _) (neg_add_cancel _)
  let exchange : S ⋙ (E Y).inverse ≅ (E X).inverse ⋙ S :=
    conjugateIsoEquiv ((E Y).toAdjunction.comp adj) (adj.comp (E X).toAdjunction)
      (tateShiftDerivedLowerStarIso i (-n) (-(2*n))).symm
  have : WeilComplex.HasUpperShriek k ℓ a :=
    WeilComplex.isLeftAdjoint_derivedLowerShriek_of_separated_base a
  let adjX := WeilComplex.derivedLowerShriekUpperShriekAdjunction (k₀ := k) (l := ℓ) a
  obtain ⟨cx⟩ := WeilComplex.purity_nonempty_shriekRightAdjoint_adicConstant_iso (d+1) adjX
  obtain ⟨push⟩ := WeilComplex.nonempty_derivedLowerShriekCompIso (k₀ := k) (l := ℓ)
    i a b (comp_over i _)
  let adjY := ((adj.ofNatIsoLeft (WeilComplex.derivedLowerShriekIsoDerivedLowerStar i).symm).comp
    adjX).ofNatIsoLeft push.symm
  obtain ⟨cy⟩ := WeilComplex.purity_nonempty_shriekRightAdjoint_adicConstant_iso d adjY
  let t (m : ℤ) := WeilSheaf.tateTwistSheaf k ℓ Y m
  let ht (m : ℤ) := WeilSheaf.isLisse_tateTwistSheaf k ℓ Y m
  let one := WeilSheaf.adicConstant k ℓ Y
  let scalar := WeilSheaf.cyclotomicUnit k ℓ
  let line : (t n).tensorObj (t (-1)) (ht n) ≅ (t d).tensorObj one (ht d) :=
    ObjectProperty.isoMk _ (WeilSheaf.tensorObjObjIsoOfIso _ _ _ (WeilSheaf.tateTwistSheafObjIso
      k ℓ Y n) (WeilSheaf.tateTwistSheafObjIso k ℓ Y (-1)) ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (show scalar ^ n * scalar ^ (-1 : ℤ) =
        scalar ^ (d : ℤ) * scalar ^ (0 : ℤ) by rw [← zpow_add, ← zpow_add]; dsimp [n]; congr 1; omega) _ ≪≫
      (WeilSheaf.tensorObjObjIsoOfIso _ _ _ (WeilSheaf.tateTwistSheafObjIso k ℓ Y d)
        (WeilSheaf.tateTwistSheafObjIso k ℓ Y 0)).symm)
  let T := WeilComplex.tateTwist k ℓ Y n
  let H := shiftFunctor (WeilComplex k ℓ Y) (2*n)
  let normalize : (E Y).inverse.obj ((WeilSheaf.toComplex.obj (t (-1)))⟦(-2 : ℤ)⟧) ≅ _ :=
    H.mapIso ((T.commShiftIso (-2 : ℤ)).app _) ≪≫
      (shiftFunctorAdd' _ (-2 : ℤ) (2*n) (2*d : ℤ) (by dsimp [n]; omega)).symm.app _ ≪≫
      (shiftFunctor _ (2*d : ℤ)).mapIso (WeilComplex.tensorLisseToComplexIso _ (ht n) _ ≪≫
        WeilSheaf.toComplex.mapIso line ≪≫ (WeilComplex.tensorLisseToComplexIso _ (ht d) _).symm)
  exact ⟨(E Y).inverse.preimageIso ((exchange.app _) ≪≫ S.mapIso cx.symm ≪≫ cy ≪≫ normalize.symm)⟩

end WeilII
