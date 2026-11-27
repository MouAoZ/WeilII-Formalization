module

public import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-! # Ordinary cohomology of an exceptional image with affine compactification -/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- In the locally closed case of Katz, Appendix A.6, an affine compactification of
dimension at most `d` bounds the ordinary cohomology of the exceptional direct image of
a constructible sheaf by `d`. Exact extension by zero produces a single constructible
sheaf on the compactification. Composition of derived direct images computes its
ordinary cohomology there, where the affine cohomological dimension bound applies. -/
public theorem isZero_cohomology_shriek_of_affineCompactification
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {B V : Scheme.{u}} (a : B ⟶ Spec (.of (AlgebraicClosure k))) [LocallyOfFiniteType a]
    (g : V ⟶ B) (c : Compactification g) [IsAffine c.Z] (d : ℕ)
    (hdim : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (M : ProEtale.AdicSheaf ℓ V) (hM : ProEtale.IsAdicConstructibleSheaf M)
    (e : ℤ) (he : d < e) :
    let E := ProEtale.adicOpenImmersionLowerShriek ℓ c.i
    let R := (ProEtale.adicLowerStar ℓ c.g).rightDerivedFunctor
    IsZero ((ProEtale.algClosedCohomology ℓ a e).obj
      (R.obj (E.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  intro E R
  have : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType (c.g ≫ a)
  have hA := hM.openImmersionLowerShriek c.i
  let A := (DerivedCategory.singleFunctor _ 0).obj (E.obj M)
  let s := (E.mapDerivedCategorySingleFunctor 0).app M
  let t := (Functor.rightDerivedFunctorCompIso' (ProEtale.adicLowerStar ℓ c.g)
    (ProEtale.adicLowerStar ℓ a) (ProEtale.adicLowerStarComp ℓ c.g a)).app A
  let post := (ProEtale.adicGlobalSections ℓ (Spec (.of (AlgebraicClosure k)))).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ e
  have hz := isZero_algClosedCohomology_of_isAffine k ℓ (c.g ≫ a) (E.obj M) hA d
    (lt_of_le_of_lt hdim (by norm_cast; omega)) e he
  exact hz.of_iso (((R ⋙ ProEtale.algClosedCohomology ℓ a e).mapIso s) ≪≫ post.mapIso t)

end WeilII
