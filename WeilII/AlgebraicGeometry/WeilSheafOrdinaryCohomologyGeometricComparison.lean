module

public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence

/-!
# Geometric coefficients of ordinary Weil sheaf cohomology

The comparison in `WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence` identifies the
carrier of constant-sheaf cohomology with derived global sections on the geometric fiber.
The same comparison of functors applies to any constructible Weil sheaf and computes the
geometric cohomology used in the affine vanishing theorem.
-/

open AlgebraicGeometry

namespace WeilII

universe u

/-- For a constructible Weil sheaf on a separated finite-type scheme over a finite field,
the carrier of its ordinary cohomology in degree `i` is linearly isomorphic to the
cohomology of its underlying adic sheaf on the geometric fiber.

Proof. Write `X` for the geometric fiber of `Z`, and `s` for the geometric fiber of `Spec k`.
The Weil direct image uses the induced map `b : X ⟶ s`. Place `M.obj` in degree zero and
take its derived Weil direct image `K`. By definition the left side is obtained from
`Hⁱ(K)` by forgetting the Weil structure, taking sections on `s`, and restricting scalars.
Forgetting is exact, and sections on `s ≅ Spec k̄` are exact since pro-étale covers of the
geometric point split. These functors therefore commute with `Hⁱ`.

Compute `K` on a K-injective resolution. Forgetting the Weil structure preserves
K-injectives and turns the Weil direct image into the adic direct image along `b`.
Sections of this direct image on `s` are sections on `X`. Forgetting also commutes with
placing a sheaf in degree zero, so the resulting complex computes `RΓ(X, M.carrier[0])`.
This is the functor comparison used in `WeilSheaf.cohomologyCarrierIso`, evaluated at `M`.

Now let `ā : X ⟶ Spec k̄` be the geometric structure map. Its direct image preserves
K-injectives because pullback is exact. Applying `ā_*` to a K-injective resolution of
`M.carrier[0]` and taking sections on `Spec k̄` thus computes `RΓ(Spec k̄, Rā_* M.carrier[0])`.
Term by term these sections are the sections on `X` of the resolution. Taking `Hⁱ` identifies
the result with `ProEtale.algClosedCohomology` along `ā`. Restricting scalars along
`ℚ̄_ℓ ≃+* ULift ℚ̄_ℓ` gives the required linear equivalence. -/
public theorem nonempty_cohomologyCarrier_linearEquiv_algClosedCohomology
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))] (M : WeilSheaf k ℓ Z) (i : ℤ) :
    Nonempty ((M.cohomology i).carrier ≃ₗ[PadicAlgCl ℓ]
      (WeilCoefficients.toModuleCat ℓ).obj ((ProEtale.algClosedCohomology ℓ
        (Z ↘ Spec (CommRingCat.of k)).geometricFiberToAlgebraicClosure i).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.carrier))) :=
  open CategoryTheory Endofunctor in by
  let : (Spec (.of k)).Over (Spec (.of k)) := instOverClass
  let a := Z ↘ Spec (.of k)
  have : a.IsOver (Spec (.of k)) := ⟨Category.comp_id a⟩
  let ha := comp_over a (Spec (.of k))
  let b := Scheme.Hom.geometricFiberMap a ha
  let N := (DerivedCategory.singleFunctor _ 0).obj M.obj
  let K := (ProEtaleWeilSheaf.lowerStar k ℓ a).rightDerivedFunctor.obj N
  let U := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ (Spec (.of k)))).comp
    (ProEtale.adicGlobalSections ℓ (Spec (.of k) ↘ Spec (.of k)).geometricFiber)
  let forgetIso := (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetCompIso
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso ℓ a ha)
    (ProEtale.adicLowerStarCompGlobalSectionsIso ℓ b)).app N
  let singleIso :=
    ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ Z)).mapDerivedCategorySingleFunctor 0).app
      M.obj
  let sections := ProEtale.adicGlobalSections ℓ a.geometricFiber
  let geomIso := (Functor.rightDerivedFunctorCompIso'
    (ProEtale.adicLowerStar ℓ a.geometricFiberToAlgebraicClosure)
    (ProEtale.adicGlobalSections ℓ (Spec (.of (AlgebraicClosure k))))
    (ProEtale.adicLowerStarCompGlobalSectionsIso ℓ a.geometricFiberToAlgebraicClosure)).symm.app
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier)
  let derivedIso := forgetIso.trans ((sections.rightDerivedFunctor.mapIso singleIso).trans geomIso)
  exact ⟨WeilCoefficients.linearEquivOfIso (((U.mapDerivedCategoryHomologyFunctorIso i).app K).trans
    ((DerivedCategory.homologyFunctor _ i).mapIso derivedIso))⟩

end WeilII
