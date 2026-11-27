module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
import WeilConjectures.SixFunctors.ProEtale.BaseChange.UnboundedComparisonBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
import WeilConjectures.TraceFormula.ExternalProductExtendScalars
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness
import WeilII.AlgebraicGeometry.EtaleGenericDirectImageBaseChange
import WeilII.AlgebraicGeometry.NativeExchangeIsIso

/-!
# Generic base change for direct image of a geometric adic sheaf

SGA 4½, *Théorèmes de finitude* 1.9(ii), p. 236, gives generic base change for finite
coefficients. Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.3,
p. 220, uses passage to fibres over a dense open of the hyperplane parameter space.
-/

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

universe u

/-- For a fixed constructible geometric adic sheaf `A` on `T`, there is a dense open in the
integral parameter scheme `S` on which every rational fibre commutes with `Rh_*` on `A[0]`.
The map is the derived pullback–direct-image mate for the cartesian square of `h : T ⟶ Y`
over the chosen fibre of `Y ⟶ S` (Katz, Appendix A.3, p. 220).

Proof. The schemes are of finite type over a field, hence noetherian. The native-to-condensed
coefficient equivalence preserves constructibility and is exact, so it takes `A[0]` to a
bounded constructible complex `K`. Choose an integral model `K₀` over the ring of integers of
a finite extension of `ℚ_ℓ` whose scalar extension is `K`. Its first derived residue-field
reduction is pulled back from a bounded constructible complex `C` on the small étale site of
`T`. Fix these choices before selecting an open.

Compactify `h` as an open immersion `j : T ↪ Z` followed by a proper map `p : Z ⟶ Y`.
The residue field of the coefficient ring is finite of characteristic `ℓ`, invertible on
`S`. For each nonzero cohomology sheaf of `C`, apply finite-coefficient generic base change
(SGA 4½, *Théorèmes de finitude* 1.9(ii)) to `j` over `S`. Take the intersection of the
resulting opens, taking all of `S` for an empty intersection. There are only finitely many
opens, each containing the generic point of the integral scheme `S`, so the intersection
is dense.

Fix a rational point in this open. Its spectrum is noetherian, so the open-immersion
comparison is invertible on each cohomology sheaf of `C` placed in degree zero. The two
functors are triangulated and the comparison commutes with shifts. Induction on the finite
truncation tower therefore gives invertibility on `C`. Proper base change for torsion
coefficients applies to `p` on `Rj_* C`. Pasting the two squares of the compactification and
using the composition isomorphisms for direct images gives the comparison for `h` on `C`.

Both `h` and its base change are quasi-compact and quasi-separated. The étale-to-pro-étale
direct-image comparisons are invertible on the bounded-below complex `C` and its pullback.
Their compatibility with the base-change maps identifies the pro-étale comparison on the
reduction of `K₀` with the image of the étale comparison. Since the target fibre is
noetherian, derived Nakayama gives invertibility of the integral comparison on `K₀`.
Extension of scalars identifies its image with the comparison on `K`. Under the coefficient
equivalence, the image of the native mate is isomorphic as an arrow to the underlying
condensed comparison on `K`. The equivalence reflects isomorphisms, proving the claim at
this point. The choices determining the open depend only on the original data. -/
public theorem exists_denseOpen_isIso_adicDerivedBaseChange_onFibers
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {S Y T : Scheme.{u}} [IsIntegral S] :
    let k := AlgebraicClosure k₀
    let pt := Spec (CommRingCat.of k)
    ∀ (a : S ⟶ pt) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      (p : Y ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
      (h : T ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (A : AdicSheaf ℓ T), IsAdicConstructibleSheaf A →
      ∃ W : S.Opens, Dense (W : Set S) ∧
        ∀ (s : pt ⟶ S), s ≫ a = 𝟙 pt → s (IsLocalRing.closedPoint k) ∈ W →
          ∀ {Ys Ts : Scheme.{u}} {iY : Ys ⟶ Y} {ps : Ys ⟶ pt}, IsPullback iY ps p s →
            ∀ {iT : Ts ⟶ T} {hs : Ts ⟶ Ys} (sq : IsPullback iT hs h iY),
              IsIso ((adicDerivedBaseChange ℓ sq.toCommSq).app
                ((DerivedCategory.singleFunctor _ 0).obj A)) :=
  open scoped CategoryTheory.Obj CategoryTheory.Functor in
  open CategoryTheory.Limits ProEtale.CondensedRing MonObj MonoidalCategory in by
  classical
  intro k pt a _ _ _ p _ _ _ h _ _ _ A hA
  have : Fact (ringChar k).Prime :=
    ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
  have : Fact (ringChar k ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (h ≫ p ≫ a)
  let U (B : Scheme.{u}) :=
    nativeExchangeEncodingAt ℓ (Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)) rfl B
  have (B : Scheme.{u}) : (U B).Additive := nativeExchangeEncodingAt_additive ℓ _ rfl B
  have (B : Scheme.{u}) : (U B).IsEquivalence := nativeExchangeEncodingAt_isEquivalence ℓ _ rfl B
  let M := (DerivedCategory.singleFunctor _ 0).obj A
  let F := (adicSheafEquivCondensedMod ℓ T).functor.obj A
  let (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] (B : Scheme.{u}) :
      MonObj (condensedRingObj R B) := (upperStarFromPoint B).monObjObj R
  let single : PadicAlgClConstructible T ℓ :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj F,
      (boundedConstructible_singleFunctor_obj_zero_iff _ F).2 hA.isConstructibleModuleObject⟩
  let eA : (U T).obj A ≅ F := by
    simpa only [U, nativeExchangeEncodingAt, nativeExchangeEncoding, F] using
      (forgetAbCompComapNativeModuleCoefficientIso ℓ T).app A
  let e : (U T).mapDerivedCategory.obj M ≅ single.obj :=
    ((U T).mapDerivedCategorySingleFunctor 0).app A ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eA
  let K : PadicAlgClConstructible T ℓ := ⟨(U T).mapDerivedCategory.obj M,
    (boundedConstructible _).prop_of_iso e.symm single.property⟩
  obtain ⟨E, K₀, ⟨eK⟩⟩ := exists_padicAlgCl_iso_integralModel T ℓ K
  obtain ⟨C, hC, ⟨eC⟩⟩ := boundedConstructible_derivedReduction_obj T ℓ E.1 K₀.obj K₀.property
  let Λ := ResidueFieldCoeff.{u} ℓ E.1
  have : HasInvertibleExponent Λ S := hasInvertibleExponent_residueFieldCoeff ℓ E a
  obtain ⟨W, hWd, hW⟩ := exists_denseOpen_isIso_etaleDerivedBaseChange Λ a p h C hC
  refine ⟨W, hWd, ?_⟩
  intro s hsa hsW Ys Ts iY ps sy iT hs sq
  have hsRange : Set.range s ⊆ (W : Set S) := by
    rintro _ ⟨x, rfl⟩
    change s x ∈ W
    rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
    exact hsW
  have : LocallyOfFiniteType ps := MorphismProperty.of_isPullback sy inferInstance
  have : IsSeparated ps := MorphismProperty.of_isPullback sy inferInstance
  have : QuasiCompact ps := MorphismProperty.of_isPullback sy inferInstance
  have : LocallyOfFiniteType hs := MorphismProperty.of_isPullback sq inferInstance
  have : IsSeparated hs := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiCompact hs := MorphismProperty.of_isPullback sq inferInstance
  have : IsNoetherian Ys := isNoetherian_of_locallyOfFiniteType ps
  let d := hC.1.1.choose
  have : C.IsGE d := hC.1.1.choose_spec
  let Cs := (Etale.upperStar (ModuleCat.{u + 1} Λ) iT).leftDerivedFunctor.obj C
  have : Cs.IsGE d := Etale.isGE_leftDerivedUpperStar_obj (ModuleCat.{u + 1} Λ) iT C d
  have hcomp := isIso_derivedBaseChangeMap_app_comparisonUpperStar Λ sq C
    (hW s hsRange sy sq)
    (unboundedDirectImageComparison_boundedBelow Λ h C d)
    (unboundedDirectImageComparison_boundedBelow Λ hs Cs d)
  let τ := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq
  have hred : IsIso (τ.app ((derivedReduction T ℓ E.1).obj K₀.obj)) := by
    with_reducible exact (NatTrans.isIso_app_iff_of_iso τ eC).mp hcomp
  -- Present the fibre square over k with its given scheme maps as projections.
  let X : Over (Spec (CommRingCat.of k)) := ⟨T, ⟨⟨⟩⟩, h ≫ p ≫ a⟩
  let B : Over (Spec (CommRingCat.of k)) := ⟨Y, ⟨⟨⟩⟩, p ≫ a⟩
  let X' : Over (Spec (CommRingCat.of k)) := ⟨Ts, ⟨⟨⟩⟩, hs ≫ ps⟩
  let B' : Over (Spec (CommRingCat.of k)) := ⟨Ys, ⟨⟨⟩⟩, ps⟩
  let overMap {P Q : Over pt} (v : P.left ⟶ Q.left) (w : v ≫ Q.hom = P.hom) : P ⟶ Q :=
    ⟨v, eqToHom (Subsingleton.elim _ _), by
      change v ≫ Q.hom = P.hom ≫ 𝟙 _
      simpa only [Category.comp_id] using w⟩
  let f : X ⟶ B := overMap h rfl
  let f' : X' ⟶ B' := overMap hs rfl
  let g : B' ⟶ B := overMap iY (by
    change iY ≫ p ≫ a = ps
    rw [← Category.assoc, sy.w, Category.assoc, hsa, Category.comp_id])
  let g' : X' ⟶ X := overMap iT (by
    change iT ≫ h ≫ p ≫ a = hs ≫ ps
    rw [← Category.assoc, sq.w, Category.assoc]
    exact congrArg (hs ≫ ·) (Over.w g))
  have q : IsPullback g' f' f g :=
    IsPullback.of_map (Over.forget pt) (Over.OverMorphism.ext sq.w) sq
  have : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (h ≫ p ≫ a))
  have : IsSeparated X.hom := inferInstanceAs (IsSeparated (h ≫ p ≫ a))
  have : QuasiCompact X.hom := inferInstanceAs (QuasiCompact (h ≫ p ≫ a))
  have : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (p ≫ a))
  have : IsSeparated B.hom := inferInstanceAs (IsSeparated (p ≫ a))
  have : QuasiCompact B.hom := inferInstanceAs (QuasiCompact (p ≫ a))
  have : LocallyOfFiniteType X'.hom := inferInstanceAs (LocallyOfFiniteType (hs ≫ ps))
  have : IsSeparated X'.hom := inferInstanceAs (IsSeparated (hs ≫ ps))
  have : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact (hs ≫ ps))
  have : LocallyOfFiniteType B'.hom := inferInstanceAs (LocallyOfFiniteType ps)
  have : IsSeparated B'.hom := inferInstanceAs (IsSeparated ps)
  have : QuasiCompact B'.hom := inferInstanceAs (QuasiCompact ps)
  have : IsNoetherian B'.left := ‹IsNoetherian Ys›
  have sqL : IsPullback g'.left f'.left f.left g.left := sq
  have hint : IsIso ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ (k := k) E.1
      (f := f) (g := g) (f' := f') (g' := g') q.toCommSq).app K₀) := by
    with_reducible
      exact isIso_boundedConstructibleBaseChange_integral_app_of_reduction ℓ
        (k := k) E.1 (f := f) (g := g) (f' := f') (g' := g') q.toCommSq sqL K₀ hred
  obtain ⟨α⟩ := nonempty_arrowIso_boundedConstructibleBaseChange_integralToPadicAlgCl
    ℓ (k := k) E (f := f) (g := g) (f' := f') (g' := g') q.toCommSq sqL K₀
  have hrat : IsIso ((boundedConstructibleBaseChange ℓ q.toCommSq).app K) := by
    apply (NatTrans.isIso_app_iff_of_iso (boundedConstructibleBaseChange ℓ q.toCommSq) eK).mp
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).1 (by
      simp only [MorphismProperty.isomorphisms.iff]
      infer_instance)
  let R := Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)
  have hrest := isIso_condensedBaseChangeOfPreserves_of_standard ℓ k q.toCommSq
    (rationalCoefficientPushforwardPreservation ℓ R (Or.inr rfl)) K hrat
  exact isIso_adicDerivedBaseChange_of_condensed ℓ k R rfl q M K (Iso.refl _) hrest

end WeilII
