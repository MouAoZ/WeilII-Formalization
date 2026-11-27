module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilII.HomologicalAlgebra.BifunctorHomSingle
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedHomComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
import WeilConjectures.TateTwist.Pullback
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryHomTransport

/-!
# Derived internal Hom from a lisse sheaf into a shifted Tate line

SGA 4, XVIII, 3.2.6, p. 586, computes the internal dual of a locally constant constructible
sheaf with finite coefficients. Here the source is finite locally free over the geometric
`ℚ̄_ℓ` coefficient sheaf, and the target is a Tate line in the condensed model.
-/

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- For a lisse sheaf `M` on `Z`, the derived internal Hom from `E_Z(M[0])` into the Tate line
`ℚ̄_ℓ,Z(m)[n]` is naturally isomorphic to `E_Z(𝓗om(M,T)[0])[n]` in the bounded constructible
category. Here `T` is the native pullback of the Tate line at the base point, and `E_Z` is the
derived coefficient equivalence. Both functors act by precomposition in `M`.

Proof (SGA 4, XVIII, 3.2.6, before (3.2.6.1), for finite coefficients). Write `E` for the
equivalence on sheaves and `L` for the condensed Tate line on `Z`. The pullback comparison
for `E`, its counit at the Tate line on the point and the pullback formula for Tate twists give
`E(T) ≅ L`. The ordinary internal Hom comparison identifies `E(𝓗om(M,B))` with
`[E(M),E(B)]` naturally in both variables. The first internal Hom is a right adjoint, and
lisseness makes it preserve finite colimits, so both internal Hom functors in `B` are exact.

Choose one K-injective resolution `L[0][n] ⟶ I` of the target for all sources. The single-degree
comparison identifies `E_Z(M[0])` with `E(M)[0]`. The derived internal Hom is represented by
the Hom complex from this single to `I`. In degree `r`, projection onto source degree zero
identifies the product with `[E(M),Iʳ]` since the factors at all other source degrees are zero.
The projected differential is induced by the differential of `I`. Exactness then gives a
quasi-isomorphism from `[E(M),L][0][n]` to this complex. Invert it in the derived category and
apply the Tate and ordinary internal Hom comparisons to identify the result with
`E_Z(𝓗om(M,T)[0])[n]`. Projection commutes with precomposition, as does the map induced by
the fixed resolution. These identifications therefore give a natural isomorphism in the source.

A lisse sheaf is constructible on the single stratum `Z`, so its degree-zero complex is bounded
constructible in both coefficient models. The shifted Tate line is bounded constructible,
and so is the derived internal Hom. Transport this property to the shifted ordinary Hom along
the comparison. Fullness lifts the component isomorphisms and faithfulness gives naturality. -/
public theorem nonempty_lisseDerivedHomIntoTateLineIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (Z : Over (Spec (CommRingCat.of (AlgebraicClosure k₀))))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (m n : ℤ) :
    letI : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
      ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ CharP.prime_ringChar k₀⟩
    letI : Fact (ringChar (AlgebraicClosure k₀) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
    let s := Spec (CommRingCat.of (AlgebraicClosure k₀))
    let T := (ProEtale.adicUpperStar ℓ Z.hom).obj
      ((ProEtale.adicSheafEquivCondensedMod ℓ s).inverse.obj (ProEtale.tateTwist s ℓ m))
    let ι := (ProEtale.adicLisseSheaf ℓ Z.left).ι
    let single := DerivedCategory.singleFunctor _ 0 ⋙
      (ProEtale.adicSheafDerivedEquivCondensedMod ℓ Z.left).functor
    let K := ι ⋙ single
    let N := ι.op ⋙ (ProEtaleWeilSheaf.ordinaryIhomBifunctor ℓ Z.left).flip.obj T ⋙
      single ⋙ shiftFunctor _ n
    let bc := ProEtale.boundedConstructible (ProEtale.condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) Z.left)
    let L := ProEtale.CondensedRing.boundedConstructibleTateTwist ℓ Z m n
    ∃ (hK : ∀ M, bc (K.obj M)) (hN : ∀ M, bc (N.obj M)),
      Nonempty ((bc.lift K hK).op ⋙ (ProEtale.CondensedRing.boundedConstructibleHom ℓ Z).flip.obj L
        ≅ bc.lift N hN) := by
  classical
  intro s T ι single K N bc L
  have : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
    ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ CharP.prime_ringChar k₀⟩
  have hchar : Fact (ringChar (AlgebraicClosure k₀) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
  let E := (ProEtale.adicSheafEquivCondensedMod ℓ Z.left).functor
  let U := ProEtaleWeilSheaf.ordinaryCondensedFunctor ℓ Z.left
  let F := U.mapDerivedCategory
  let eU : U ≅ E := ProEtale.forgetAbCompComapNativeModuleCoefficientIso ℓ Z.left
  let eF : F ≅ (ProEtale.adicSheafDerivedEquivCondensedMod ℓ Z.left).functor :=
    Functor.mapDerivedCategoryNatIso eU
  have hK (M) : bc (K.obj M) := by
    have := isNoetherian_of_locallyOfFiniteType Z.hom
    apply bc.prop_of_iso ((E.mapDerivedCategorySingleFunctor 0).app (ι.obj M)).symm
    apply ProEtale.CondensedRing.boundedConstructible_singleFunctor_zero_obj
    exact (ProEtale.isAdicConstructibleSheaf_iff_isConstructibleModuleObject ℓ k₀ _
      Z M.obj).1 (ProEtale.IsAdicLisseSheaf.isAdicConstructibleSheaf M.property)
  have : NeZero (ℓ : AlgebraicClosure k₀) :=
    ⟨fun h ↦ hchar.out (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _
      ((ringChar.spec (AlgebraicClosure k₀) ℓ).1 h)).resolve_left CharP.ringChar_ne_one)⟩
  let eT : U.obj T ≅ ProEtale.tateTwist Z.left ℓ m :=
    eU.app T ≪≫ (ProEtale.adicUpperStarCompCondensedModIso ℓ Z.hom).app _ ≪≫
      (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) Z.hom).mapIso
        ((ProEtale.adicSheafEquivCondensedMod ℓ s).counitIso.app _) ≪≫
      ProEtale.upperStarTateTwistIso ℓ Z.hom (𝟙 s) m
  let S := (CochainComplex.singleFunctor _ (-n)).obj T
  obtain ⟨I, hI, g, _, hg⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective S
  let shiftSingle := (DerivedCategory.singleFunctors (ProEtale.AdicSheaf ℓ Z.left)).shiftIso
    n (-n) 0 (add_neg_cancel n)
  let eL : F.obj (DerivedCategory.Q.obj I) ≅ L.obj :=
    F.mapIso (asIso (DerivedCategory.Q.map g)).symm ≪≫
      (U.mapDerivedCategorySingleFunctor (-n)).app T ≪≫
      (DerivedCategory.singleFunctor _ (-n)).mapIso eT ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (add_neg_cancel n)).symm.app _
  let H := ProEtaleWeilSheaf.ordinaryIhomBifunctor ℓ Z.left
  let P := ι ⋙ CochainComplex.singleFunctor _ 0
  let K₀ := ι ⋙ DerivedCategory.singleFunctor _ 0
  let V := ι.op ⋙ H.flip.obj T
  let hpre := ProEtaleWeilSheaf.precompQuasiIso_ordinaryIhomBifunctor ℓ Z.left I
  let eQ : K₀.op ⋙ DerivedCategory.bifunctorRHomOfComplex H I ≅
      P.op ⋙ DerivedCategory.bifunctorHomQFunctor H I :=
    NatIso.ofComponents (fun M ↦ DerivedCategory.bifunctorRHomOfComplexQObjIso H hpre
      (P.obj M.unop)) (fun f ↦ DerivedCategory.bifunctorRHomOfComplexQObjIso_hom_naturality
        hpre (P.map f.unop))
  obtain ⟨eS⟩ := nonempty_bifunctorHomQSingleIso H ι T (-n) I g
    (fun M ↦ by
      have := (CategoryTheory.Mod.ihomAdjunction M.obj).rightAdjoint_preservesLimits
      exact inferInstanceAs (Limits.PreservesFiniteLimits (ProEtale.AdicSheaf.ihom M.obj)))
    (fun M ↦ ProEtale.IsAdicLisseSheaf.preservesFiniteColimits_ihom M.property)
  let eK : K₀ ⋙ F ≅ K := Functor.isoWhiskerLeft K₀ eF
  let RH := ProEtale.CondensedRing.derivedHom (Profinite.padicAlgClRingObj ℓ) Z.left
  let e : K.op ⋙ RH.flip.obj L.obj ≅ N :=
    Functor.isoWhiskerRight (NatIso.op eK) _ ≪≫
      Functor.isoWhiskerLeft K₀.op (ProEtaleWeilSheaf.ordinaryRHomCondensedIso ℓ Z.left eL).symm ≪≫
      Functor.isoWhiskerRight (eQ ≪≫ eS) F ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft V shiftSingle.symm) F ≪≫
      Functor.isoWhiskerLeft (V ⋙ DerivedCategory.singleFunctor _ 0)
        ((F.commShiftIso n) ≪≫ Functor.isoWhiskerRight eF (shiftFunctor _ n))
  let D := (bc.lift K hK).op ⋙ (ProEtale.CondensedRing.boundedConstructibleHom ℓ Z).flip.obj L
  have hN (M) : bc (N.obj M) := bc.prop_of_iso (e.app M) (D.obj M).property
  refine ⟨hK, hN, ⟨(bc.fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩⟩
  exact e

end WeilII
