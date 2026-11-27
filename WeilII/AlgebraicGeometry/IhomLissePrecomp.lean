module

public import WeilConjectures.WeilSheaf.DerivedHom

/-!
# Precomposition in the derived internal Hom of a lisse Weil sheaf

The coefficient action comes from `ProEtaleWeilSheaf.ihomBifunctor` in
`WeilConjectures.WeilSheaf.DerivedHom`. Its right derived transformation restricts to the
bounded constructible subcategory used by `WeilComplex.ihomLisse` in
`WeilConjectures.WeilSheaf.Fourier`.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- A morphism `f : A ⟶ A'` of lisse Weil sheaves acts on `R𝓗om(A', −)` by precomposition.
Derive the coefficient map of `ProEtaleWeilSheaf.ihomBifunctor` using
`Functor.rightDerivedFunctorNatTrans` from `RightDerivedFunctor.Comp`, then restrict its
components to bounded constructible Weil complexes. -/
@[expose] public noncomputable def ihomLissePrecomp
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {A A' : WeilSheaf k ℓ X} (f : A ⟶ A') (hA : A.IsLisse) (hA' : A'.IsLisse) :
    WeilComplex.ihomLisse A' hA' ⟶ WeilComplex.ihomLisse A hA :=
  ObjectProperty.liftFullSubcategoryMap _ _
    (Functor.rightDerivedFunctorNatTrans ((ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map f.hom.op))
    (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor A' hA')
    (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor A hA)

end WeilII
