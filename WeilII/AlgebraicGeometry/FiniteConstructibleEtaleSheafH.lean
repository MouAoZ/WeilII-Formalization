module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleExtFinite

/-! # Finiteness for ordinary cohomology of a constructible étale sheaf -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Over a separably closed field, a finite-type scheme has finite ordinary cohomology
with constructible finite coefficients of invertible exponent. This expresses the finiteness
theorem (SGA 4½, Théorèmes de finitude, 1.1) using the underlying abelian sheaf. -/
public theorem finite_functorH_constructible_etale {k : Type u} [Field k] [IsSepClosed k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    (q : ℕ) :
    Finite ((Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) Ab)).obj F)) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  have hHom := Etale.finite_hom_constantComplex_shift a F (q : ℤ)
  have hH := Finite.of_equiv _ (Etale.homConstantComplexLinearEquivCohomology Λ X K q).toEquiv
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
  obtain ⟨e'⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  exact @Finite.of_equiv _ _ hH ((e.app F) ≪≫ (e'.app _).symm).addCommGroupIsoToAddEquiv.toEquiv

end WeilII
