module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.TraceFormula.PointFiberFunctor
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalar
import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
import WeilII.AlgebraicGeometry.PointSectionsAdicComparison

/-!
# The condensed point fiber and native adic derived global sections

On a separably closed point the condensed fiber is evaluation on the regular module, derived
termwise. Comparison with native adic global sections uses the action of the coefficient field
on that module. See `TraceFormula/PointFiberFunctor.lean` and the adic comparison in
`SixFunctors/ProEtale/Adic/CondensedModelScalar.lean` in *Weil Conjectures*.
-/

open AlgebraicGeometry CategoryTheory ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- On the spectrum of a separably closed field of positive characteristic different from `ℓ`,
the condensed fiber on bounded constructible complexes is naturally isomorphic to native
adic derived global sections after transport by the inverse derived equivalence. The
isomorphism takes values in the derived category of `WeilCoefficients ℓ`.

Proof (using *Weil Conjectures*, `Adic/GlobalSectionsHom.lean`, `Adic/CondensedModelScalar.lean`,
`Adic/CondensedModelDerived.lean`, and `TraceFormula/PointFiberFunctor.lean`).
Write `A` for the equivalence on sheaves, `G` for native global sections, and `S` for condensed
point sections. Let `u : A(U_ad) ≅ U` be the isomorphism of regular modules. Given a section
`x ∈ G(M)`, evaluation at one gives a unique `v : U_ad ⟶ M` with `v(1) = x`. Send `x` to
`u.inv ≫ A.map v` in `S(A(M)) = Hom(U,A(M))`. Evaluation at one, full faithfulness of `A`,
and precomposition by `u.inv` are additive bijections. For a lifted scalar `a`, the map
representing `a • x` is `v` precomposed with multiplication by `a`. Conjugating its scalar
endomorphism by `u` gives multiplication by the constant section `a.down` on `U`, precisely
the precomposition action defining `S`. The bijection is therefore coefficient-linear.
For a map `f : M ⟶ N`, the section `G(f)(x)` is represented by `v ≫ f`, giving naturality.

Thus `G ≅ A ⋙ S`. Precompose with the inverse equivalence `L` and apply `S` to the counit
to obtain `L ⋙ G ≅ S`. Since the field is separably closed, the condensed regular module is
projective. Its Hom functor is exact and restriction of scalars is exact, so the termwise
derived functor `D(S)` computes `RS`. The exact equivalence `L` preserves K-injectives:
maps from an acyclic complex into `L(I)` correspond to maps from its acyclic image under
`A` into `I`, and the equivalence transports null homotopies. Hence applying `L` to a
K-injective resolution computes the composite, giving `RS ≅ D(L) ⋙ RG`. Here `D(L)` is the
inverse derived model equivalence. Precompose with the bounded constructible inclusion.
Its composite with `D(S)` is the point fiber by definition. -/
public theorem nonempty_pointFiberFunctorIsoAdicRightDerivedGlobalSections
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    let s := (point k).left
    Nonempty (pointFiberFunctor ℓ k ≅ (ProEtale.boundedConstructible _).ι ⋙
      (ProEtale.adicSheafDerivedEquivCondensedMod ℓ s).inverse ⋙
      (ProEtale.adicGlobalSections ℓ s).rightDerivedFunctor) :=
  open ProEtale in by
  intro s
  let A := adicSheafEquivCondensedMod ℓ s
  let Γ := adicGlobalSections ℓ s
  let S := pointSections ℓ k
  have comparison : A.inverse ⋙ Γ ≅ S := (pointSectionsAdicComparison ℓ k).inverseCompIso
  have : A.symm.functor.Additive := inferInstanceAs (adicSheafEquivCondensedMod ℓ s).inverse.Additive
  have : A.inverse.PreservesKInjectiveComplexes := A.symm.preservesKInjectiveComplexes_functor
  exact ⟨Functor.isoWhiskerLeft (boundedConstructible _).ι
    (S.rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      Functor.rightDerivedFunctorIsoMapDerivedCategoryComp comparison)⟩

end WeilII
