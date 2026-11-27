module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
import WeilII.AlgebraicGeometry.EtaleDerivedTensorOppositeShifts

/-! # Opposite shifts in the tensor comparison for étale coefficient reduction -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

/-- Apply `WeilII.etaleLeftDerivedTensor_oppositeShifts` to sheaf extension of
scalars and its adjunction to exact restriction. Extension preserves flats and
preserves K-flat quasi-isomorphisms by `preservesKFlatQuasiIso_extendScalars`.
The functor in this specialization is `derivedExtendScalars` by definition. Its
adjoint-induced shift is `derivedExtendScalarsCommShift` by the definition of
`derivedExtendScalarsAdjunction`. Finally
`derivedExtendScalarsDerivedTensorIso_hom` followed by
`Functor.leftDerivedFunctorMonoidal_δ` identifies each direct tensor component
with the component of the native left-derived tensor comparison. Substituting
these identifications in the native cancellation square gives this equation.
See `Purity/Smooth/ReductionMonoidal.lean` and `ReductionTateTwist.lean`. -/
theorem etaleReductionTensorShiftCancellation {A B : Type (u+1)} [CommRing A] [CommRing B]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (X : Scheme.{u}) (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))) :
    let Ψ := derivedExtendScalars hρ ha X
    letI := derivedExtendScalarsCommShift hρ ha X
    let cancel (R : Type (u+1)) [CommRing R]
        (P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R))) :=
      (derivedTensorShiftIso _ P N (2 : ℤ) (-2)).hom ≫
        (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _
    Ψ.map (cancel A K M) ≫ (derivedExtendScalarsDerivedTensorIso hρ ha X K M).hom =
      (derivedExtendScalarsDerivedTensorIso hρ ha X _ _).hom ≫
        derivedTensorHom (ModuleCat.{u+1} B) ((Ψ.commShiftIso (2 : ℤ)).hom.app K)
          ((Ψ.commShiftIso (-2 : ℤ)).hom.app M) ≫ cancel B (Ψ.obj K) (Ψ.obj M) := by
  intro Ψ cancel
  let := preservesKFlatQuasiIso_extendScalars hρ ha X
  let E := Sheaf.extendScalars X.smallEtaleTopology ρ
  have h := etaleLeftDerivedTensor_oppositeShifts (ModuleCat.{u+1} A) (ModuleCat.{u+1} B)
    E (Sheaf.restrictScalars X.smallEtaleTopology ρ)
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ) K M
  have hδ (P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))) :
      (derivedExtendScalarsDerivedTensorIso hρ ha X P N).hom =
        (E.leftDerivedTensorComparison.app P).app N := by
    refine (derivedExtendScalarsDerivedTensorIso_hom hρ ha X P N).trans
      (Eq.trans ?_ (E.leftDerivedFunctorMonoidal_δ P N))
    apply eq_of_heq
    apply Functor.OplaxMonoidal.δ.hcongr_10 <;> rfl
  rw [hδ, hδ]
  dsimp only [cancel] at *
  refine Eq.mp ?_ h
  -- Apply congruence to the square and its components while the natural transformations
  -- are still visible. Reducing their projections unfolds the derived adjunction.
  repeat' (run_tac Lean.Elab.Tactic.liftMetaTactic fun g ↦ g.withContext do
    let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let some (a, b) := (t.eq?.map fun (_, a, b) ↦ (a, b)).orElse
      (fun _ ↦ t.heq?.map fun (_, a, _, b) ↦ (a, b)) | failure
    let a := a.consumeMData
    let b := b.consumeMData
    guard (a != b && a.getAppFn == b.getAppFn)
    let heads := [``Eq, ``CategoryStruct.comp, ``derivedTensorHom, ``NatTrans.app]
    guard (heads.contains (a.getAppFn.constName?.getD .anonymous))
    let some gs ← g.hcongr? | failure
    return gs)
  all_goals rfl

end WeilII
