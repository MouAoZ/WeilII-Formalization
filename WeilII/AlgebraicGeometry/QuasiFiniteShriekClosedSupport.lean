module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.WeilSheaf.FiniteLowerStar

/-!
# Cohomology of a quasi-finite exceptional direct image on a closed support

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.5, p. 221,
uses exactness of the quasi-finite exceptional direct image. The open–closed triangle on
the same page computes its ordinary cohomology on a closed subscheme containing the image.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Let `g : V ⟶ B` be quasi-finite between separated schemes of finite type over the
algebraic closure of a finite field. If its image lies in the image of a closed immersion
`i : Z ⟶ B`, then for each constructible sheaf `M` on `V` there is a constructible sheaf
`A` on `Z` with `Hᵐ(B, Rg_! M) ≅ Hᵐ(Z, A)` in every integer degree.

Proof (Katz, Appendix A.5, p. 221, and the open–closed triangle preceding A.6).
The closed graph of `g` factors it through the projection from the product of `V` and `B`
over the field. Thus `g` is separated of finite type, and locally of finite presentation
over the noetherian base `B`. By Zariski's main theorem write `g = p ∘ v` with `v` a
quasi-compact open immersion and `p` finite and locally of finite presentation. This gives
a compactification. To compare it with `c`, transport the constructible complex `M[0]`
to the equivalent condensed model, apply independence of compactification there, and
transport the isomorphism back. Thus the given exceptional direct image is `Rp_* v_! M[0]`.
Extension by zero along `v` is exact, as is pushforward along `p`, so this complex is
`F[0]` for `F = p_* v_! M`. Its degree-zero cohomology sheaf is constructible since
exceptional direct image preserves bounded constructible complexes.

For the open complement `b : U ⟶ B` of `i`, let `t` and `p_U` be the projections from
the pullback of `p` to `U`, with `t` mapping to the source of `p`. The images of `t` and
`v` are disjoint since their intersection would map to both `U` and the image of `g`.
Hence `t^* v_! M = 0`. Open base change gives `b^* F ≅ (p_U)_* t^* v_! M = 0`.
Take `A = i^* F`, which is constructible by pullback. The open complement is quasi-compact
and pullback is exact, so the closed-support unit identifies `F[0]` with `Ri_* A[0]`.
Apply the derived direct image along the structure morphism `a` of `B`. Composition
identifies `Ra_* Ri_*` with the derived direct image along `i ≫ a`. Taking derived global
sections on the geometric point and then cohomology gives the stated isomorphisms. -/
public theorem exists_constructible_cohomologyIso_of_quasiFinite_closedSupport
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {V B Z : Scheme.{u}} (a : B ⟶ Spec (CommRingCat.of (AlgebraicClosure k₀)))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] (g : V ⟶ B)
    [IsSeparated (g ≫ a)] [LocallyOfFiniteType (g ≫ a)] [QuasiCompact (g ≫ a)]
    [LocallyQuasiFinite g] (c : Compactification g) (M : ProEtale.AdicSheaf ℓ V)
    (hM : ProEtale.IsAdicConstructibleSheaf M) (i : Z ⟶ B) [IsClosedImmersion i]
    (hgi : Set.range g.base ⊆ Set.range i.base) :
    let K := ((ProEtale.adicOpenImmersionLowerShriek ℓ c.i).mapDerivedCategory ⋙
      (ProEtale.adicLowerStar ℓ c.g).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)
    ∃ A : ProEtale.AdicSheaf ℓ Z, ProEtale.IsAdicConstructibleSheaf A ∧
      ∀ m : ℤ, Nonempty ((ProEtale.algClosedCohomology ℓ a m).obj K ≅
        (ProEtale.algClosedCohomology ℓ (i ≫ a) m).obj ((DerivedCategory.singleFunctor _ 0).obj A)) := by
  classical
  intro K
  let k := AlgebraicClosure k₀
  have hk : ringChar k ≠ ℓ := Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)
  have : Fact (ringChar k ≠ ℓ) := ⟨hk⟩
  have : Fact (ringChar k).Prime := ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace a
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g a
  have : QuasiCompact g := QuasiCompact.of_comp g a
  have : IsSeparated g := IsSeparated.of_comp g a
  obtain ⟨T, v, p, hv, hvq, hp, hpf, hvp⟩ :=
    g.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation
  let c₀ : Compactification g := ⟨T, p, v, hvp.symm, inferInstance, hv⟩
  let N := (DerivedCategory.singleFunctor _ 0).obj M
  let F := (ProEtale.adicLowerStar ℓ p).obj ((ProEtale.adicOpenImmersionLowerShriek ℓ v).obj M)
  let A := (ProEtale.adicUpperStar ℓ i).obj F
  have hN : ProEtale.DerivedCategory.boundedConstructibleAdic ℓ V N := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · exact (ProEtale.adicConstructibleSheaf ℓ V).prop_of_isZero
        (DerivedCategory.isZero_of_isGE N 0 n hn)
    · exact (ProEtale.adicConstructibleSheaf ℓ V).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
    · exact (ProEtale.adicConstructibleSheaf ℓ V).prop_of_isZero
        (DerivedCategory.isZero_of_isLE N 0 n hn)
  have eK : K ≅ (DerivedCategory.singleFunctor _ 0).obj F := by
    let V' : Over (Spec (.of k)) := Over.mk (g ≫ a)
    let B' : Over (Spec (.of k)) := Over.mk a
    let g' : V' ⟶ B' := Over.homMk g rfl
    have : LocallyOfFiniteType V'.hom := inferInstanceAs (LocallyOfFiniteType (g ≫ a))
    have : IsSeparated V'.hom := inferInstanceAs (IsSeparated (g ≫ a))
    have : QuasiCompact V'.hom := inferInstanceAs (QuasiCompact (g ≫ a))
    have : LocallyOfFiniteType B'.hom := inferInstanceAs (LocallyOfFiniteType a)
    have : IsSeparated B'.hom := inferInstanceAs (IsSeparated a)
    have : QuasiCompact B'.hom := inferInstanceAs (QuasiCompact a)
    letI (X : Scheme.{u}) : MonObj (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
      Functor.monObjObj (F := ProEtale.upperStarFromPoint X) _
    let H := (ProEtale.adicSheafDerivedEquivCondensedMod ℓ V).functor.obj N
    have hH := (ProEtale.boundedConstructibleAdic_iff_boundedConstructible ℓ k₀ k V' N).1 hN
    let Hc := (⟨H, hH⟩ : (ProEtale.boundedConstructible _).FullSubcategory)
    -- Forget to the ambient condensed category before transporting the comparison back.
    let e := ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
      ℓ (f := g') c c₀
    let ec (d : Compactification g) :=
      (ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        ℓ (f := g') d).app Hc
    let em (d : Compactification g) :=
      (ProEtale.adicRightDerivedLowerShriekOfCompactificationCompIso ℓ B d).app N
    have e₀ : K ≅ (ProEtale.adicLowerStar ℓ p).rightDerivedFunctor.obj
        ((ProEtale.adicOpenImmersionLowerShriek ℓ v).mapDerivedCategory.obj N) :=
      (ProEtale.adicSheafDerivedEquivCondensedMod ℓ B).fullyFaithfulFunctor.preimageIso
        (em c ≪≫ (ec c).symm ≪≫ (ProEtale.boundedConstructible _).ι.mapIso (e.app Hc) ≪≫
          ec c₀ ≪≫ (em c₀).symm)
    have := ProEtale.preservesFiniteColimits_adicLowerStar_of_isFinite ℓ p
    exact e₀ ≪≫ (ProEtale.adicLowerStar ℓ p).rightDerivedFunctor.mapIso
      (((ProEtale.adicOpenImmersionLowerShriek ℓ v).mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (ProEtale.adicLowerStar ℓ p).singleFunctorCompRightDerivedFunctorIso.app _
  have hK : ProEtale.DerivedCategory.boundedConstructibleAdic ℓ B K :=
    ((ProEtale.boundedConstructibleAdicLowerShriekOfCompactification hk a c).obj ⟨N, hN⟩).property
  have hF : ProEtale.IsAdicConstructibleSheaf F :=
    (ProEtale.adicConstructibleSheaf ℓ B).prop_of_iso
      ((DerivedCategory.homologyFunctor _ 0).mapIso eK ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F) (hK.2 0)
  refine ⟨A, hF.upperStar i, ?_⟩
  let U := i.openComplement
  let b := U.ι
  let t := Limits.pullback.fst p b
  let q := Limits.pullback.snd p b
  have hdisj : Set.range v.base ∩ Set.range t.base = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨⟨x, rfl⟩, ht⟩
    change v x ∈ Set.range (Limits.pullback.fst p b) at ht
    rw [Scheme.Pullback.range_fst] at ht
    have hu : p (v x) ∈ (i.openComplement : Set B) := by
      simpa only [b, U, Scheme.Opens.range_ι, Set.mem_preimage] using ht
    exact hu (hgi ⟨x, congrArg (fun f : V ⟶ B ↦ f x) hvp.symm⟩)
  have ht := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek v t hdisj M
  have sq : IsPullback q t b p := (IsPullback.of_hasPullback p b).flip
  have := ProEtale.isIso_adicBaseChangeMap_of_isPullback ℓ sq
  have hb : Limits.IsZero ((ProEtale.adicUpperStar ℓ b).obj F) :=
    ((ProEtale.adicLowerStar ℓ q).map_isZero ht).of_iso
      ((asIso (ProEtale.adicBaseChangeMap ℓ sq.toCommSq)).app _)
  have hb' := ((DerivedCategory.singleFunctor _ 0).map_isZero hb).of_iso
    (((ProEtale.adicUpperStar ℓ b).mapDerivedCategorySingleFunctor 0).app F)
  have hi : IsCompl (Set.range i.base) (Set.range b.base) := by
    change IsCompl (Set.range i) (Set.range i.openComplement.ι)
    rw [i.range_eq_compl_range_openComplement_ι]
    exact isCompl_compl.symm
  have hunit := ProEtale.isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero
    i b hi (K := (DerivedCategory.singleFunctor _ 0).obj F) hb'
  let L := (DerivedCategory.singleFunctor _ 0).obj A
  have eZ : K ≅ (ProEtale.adicLowerStar ℓ i).rightDerivedFunctor.obj L :=
    eK ≪≫ asIso ((ProEtale.adicDerivedUpperStarLowerStarAdjunction ℓ i).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj F)) ≪≫
      (ProEtale.adicLowerStar ℓ i).rightDerivedFunctor.mapIso
        (((ProEtale.adicUpperStar ℓ i).mapDerivedCategorySingleFunctor 0).app F)
  intro m
  let comp := (Functor.rightDerivedFunctorCompIso' (ProEtale.adicLowerStar ℓ i)
    (ProEtale.adicLowerStar ℓ a) (ProEtale.adicLowerStarComp ℓ i a)).app L
  exact ⟨(ProEtale.algClosedCohomology ℓ a m).mapIso eZ ≪≫
    ((ProEtale.adicGlobalSections ℓ _).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ m).mapIso comp⟩

end WeilII
