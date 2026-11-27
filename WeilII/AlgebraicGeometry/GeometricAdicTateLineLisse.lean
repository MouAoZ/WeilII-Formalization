module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.TateTwist.LocallyFree

/-! # The geometric Tate line in the native coefficient category -/

namespace WeilII

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.Obj

universe u

/-- The Tate twists on the geometric point are lisse in the native adic category.
In the condensed model they are locally free of rank one, hence constructible.
The coefficient equivalence identifies constructibility, and a constructible sheaf
on the spectrum of a field is lisse. This is the Tate line in Katz A.5, pp. 220–221. -/
public theorem isAdicLisseSheaf_geometricTateLine
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (d : ℤ) :
    let K := AlgebraicClosure k
    let S := Spec (CommRingCat.of K)
    ProEtale.IsAdicLisseSheaf
      ((ProEtale.adicSheafEquivCondensedMod ℓ S).inverse.obj (ProEtale.tateTwist S ℓ d)) := by
  intro K S
  have hchar : ringChar K ≠ ℓ := Algebra.ringChar_eq k K ▸ Fact.out
  have : NeZero (ℓ : K) := ⟨fun h ↦ hchar
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec K ℓ).1 h)).resolve_left
      CharP.ringChar_ne_one)⟩
  let E := ProEtale.adicSheafEquivCondensedMod ℓ S
  let T := ProEtale.tateTwist S ℓ d
  have : IsSeparated (Over.mk (𝟙 S)).hom := inferInstanceAs (IsSeparated (𝟙 S))
  have : LocallyOfFiniteType (Over.mk (𝟙 S)).hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  have : QuasiCompact (Over.mk (𝟙 S)).hom := inferInstanceAs (QuasiCompact (𝟙 S))
  apply ProEtale.IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isField
  apply (ProEtale.isAdicConstructibleSheaf_iff_isConstructibleModuleObject ℓ k K
    (Over.mk (𝟙 S)) _).mpr
  change ProEtale.IsConstructibleModuleObject (ProEtale.condensedRingObj
    (Profinite.padicAlgClRingObj ℓ) S) (E.functor.obj (E.inverse.obj T))
  exact constructible_of_iso (E.counitIso.app T).symm
    (ProEtale.isLocallyFree_tateTwist ℓ (𝟙 S) d).isConstructibleModuleObject

end WeilII
