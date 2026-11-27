module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilII.AlgebraicGeometry.AdicOpenExtensionPullback
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
import WeilII.Paper.ProjectiveIncidenceComplementStandardChart
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilII.AlgebraicGeometry.AdicRelativeKunnethOpenUnit
import WeilII.AlgebraicGeometry.AdicOpenExtensionLocalImage
import WeilII.CategoryTheory.MateEssentialImage
import WeilII.Paper.ProjectiveIncidenceProductChart

/-!
# Extension by zero on the universal hyperplane complement

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.1–A.2,
pp. 218–219, computes the adjunction map on the product of projective space with its dual.
-/

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory Limits

universe u

/-- Katz, Lemma A.2, pp. 218–219, for a constructible sheaf in degree zero.
Write `β : B ↪ P × P∨` for the universal incidence complement, `F = f × id`,
`α : F⁻¹B ↪ X × P∨`, and `G : F⁻¹B ⟶ B` for the restriction of `F`. At
`L = (α^* pr_X^* K)[0]` the adjunction map `β_! RG_* L ⟶ RF_* α_! L` is invertible.
Its transpose under `F^* ⊣ RF_*` is the open-extension pullback isomorphism followed
by `α_!` applied to the counit of `G^* ⊣ RG_*`.

Proof. Cover the first projective space by its standard charts. On the chart `U` where
`Xₐ ≠ 0`, replace the dual coordinate `Yₐ` by `∑ᵢ (Xᵢ/Xₐ)Yᵢ`, fixing the others.
By A.1 this identifies the incidence complement with `U × V`, where `V` is the dual
chart at `a`. The automorphism and its pullback to `T = f⁻¹U` preserve the first
projections. With `h : T ⟶ U`, the vertical maps thus become `H_W = h × id_W` for
`W = V, P∨`. Write `u_T, u_U` for the products of the inclusion `V ↪ P∨` with the
two identities. Exact pullback identifies the input with `p_T^* A`, where `p_T` is the
first projection over `V` and `A = (K|T)[0]`.

Under these identifications the restricted map is the adjunction map of the product
square. Indeed, for restriction to an open, the direct-image base-change isomorphism is
the right-adjoint conjugate of open-extension pullback. Its transpose is the restricted
counit preceded by the pullback composition isomorphism. Applying this to `F` and `G`
and using naturality of open-extension pullback on the counit of `G` identifies the two
transposes. The same computation transports the map across the chart isomorphisms.

Let `p_U` be the first projection of `U × V`. Relative Künneth for the unit on `V`
gives an isomorphism `b : p_U^* Rh_* A ⟶ RH_{V*} p_T^* A`. For the unit extended by
zero from `V` to `P∨`, it gives an isomorphism
`d : u_{U!} p_U^* Rh_* A ⟶ RH_{P∨*} u_{T!} p_T^* A`. These comparisons apply since
`h` is separated of finite type, the chart inclusion is quasi-compact, and the restriction
of `K` is constructible. Precompose the product exchange map with `u_{U!} b` and transpose
along `H_{P∨}^* ⊣ RH_{P∨*}`. Naturality of open-extension pullback identifies its transpose
with `u_{T!}(ε_{H_V} ∘ H_V^* b)`, where `ε` denotes the counit. By the definition of
`b` the inner composite is `p_T^* ε_h`. This is the formula for the transpose of `d`.
Hence the precomposed map equals `d`, and the product exchange map is invertible. The opens
`U × P∨` cover the product, so their derived restrictions jointly detect invertibility. -/
public theorem isIso_universalHyperplaneExtensionByZeroExchange
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (I : Type u) [Fintype I] [Nontrivial I] {X : Scheme.{u}} :
    let S := Spec (CommRingCat.of (AlgebraicClosure k₀))
    let P := ℙ(I; S)
    let π := P ↘ S
    ∀ (f : X ⟶ P) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (K : AdicSheaf ℓ X), IsAdicConstructibleSheaf K →
      let prX := pullback.fst (f ≫ π) π
      let F := pullback.map (f ≫ π) π π π f (𝟙 P) (𝟙 S) (by simp) (by simp)
      let B := (projectiveHyperplaneIncidenceFamily I S).subschemeι.openComplement
      let α := (F ⁻¹ᵁ B).ι
      let L := (DerivedCategory.singleFunctor _ 0).obj
        ((adicUpperStar ℓ α).obj ((adicUpperStar ℓ prX).obj K))
      let G := morphismRestrict F B
      let sq := isPullback_morphismRestrict F B
      letI : IsIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq) :=
        isIso_adicOpenExtensionPullbackMap ℓ sq
      let exchange := mateEquiv (adicDerivedUpperStarLowerStarAdjunction ℓ G)
        (adicDerivedUpperStarLowerStarAdjunction ℓ F)
        (TwoSquare.mk _ _ _ _ (inv (adicOpenExtensionPullbackMap ℓ sq.toCommSq)))
      IsIso (exchange.app L) := by
  classical
  intro S P π f hfsep hft hqc K hK prX F B α L G sq
  let ff {T Z : Scheme.{u}} (j : T ⟶ Z) [IsOpenImmersion j] :
      (adicOpenImmersionLowerShriek ℓ j).mapDerivedCategory.FullyFaithful := by
    have := (Adjunction.Triple.isIso_unit_iff_isIso_counit
      ⟨adicDerivedOpenExtensionAdjunction ℓ j, adicDerivedUpperStarLowerStarAdjunction ℓ j⟩).2
      (isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion j)
    exact (adicDerivedOpenExtensionAdjunction ℓ j).fullyFaithfulLOfIsIsoUnit
  have := isIso_adicOpenExtensionPullbackMap ℓ sq
  -- The extension by zero is fully faithful, so it suffices to construct its target locally.
  apply isIso_mate_app_of_essImage (adicDerivedUpperStarLowerStarAdjunction ℓ G)
    (adicDerivedUpperStarLowerStarAdjunction ℓ F) (ff B.ι) (ff α)
    (asIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq)).symm
  apply adicDerivedOpenExtension_essImage_of_locally
  intro z
  obtain ⟨d, chart⟩ := exists_incidenceProductChart (AlgebraicClosure k₀) I f z
  let U := ProjectiveSpace.standardOpen I S d
  let T := f ⁻¹ᵁ U
  let D := Over.mk π
  let Y := Over.mk (U.ι ≫ π)
  let A := Over.mk ((f ∣_ U) ≫ Y.hom)
  let h : A ⟶ Y := Over.homMk (f ∣_ U) rfl
  let j : Y ⟶ D := Over.homMk U.ι rfl
  let iX := (prod.map (𝟙 A) j).left
  let iY := (prod.map (𝟙 Y) j).left
  let pX := (prod.fst : A ⨯ Y ⟶ A).left
  let pY := (prod.fst : Y ⨯ Y ⟶ Y).left
  obtain ⟨y, x, b, a, hy, hx, hz, q, qb, qa, hp⟩ := chart
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsOpenImmersion iX := inferInstanceAs (IsOpenImmersion (prod.map (𝟙 A) j).left)
  have : IsOpenImmersion iY := inferInstanceAs (IsOpenImmersion (prod.map (𝟙 Y) j).left)
  refine ⟨_, y, hy, hz, _, iY, inferInstance, b, qb, ?_⟩
  have : IsNoetherian P := isNoetherian_of_locallyOfFiniteType π
  have : QuasiCompact j.left := inferInstanceAs (QuasiCompact U.ι)
  have : IsSeparated h.left := inferInstanceAs (IsSeparated (f ∣_ U))
  have : LocallyOfFiniteType h.left := inferInstanceAs (LocallyOfFiniteType (f ∣_ U))
  have : QuasiCompact h.left := inferInstanceAs (QuasiCompact (f ∣_ U))
  have : LocallyOfFiniteType D.hom := inferInstanceAs (LocallyOfFiniteType (ℙ(I; S) ↘ S))
  have : QuasiCompact D.hom := inferInstanceAs (QuasiCompact (ℙ(I; S) ↘ S))
  have : IsSeparated D.hom := inferInstanceAs (IsSeparated (ℙ(I; S) ↘ S))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ D.hom))
  have : QuasiCompact Y.hom := inferInstanceAs (QuasiCompact (U.ι ≫ D.hom))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ D.hom))
  have : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (h.left ≫ Y.hom))
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (h.left ≫ Y.hom))
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (h.left ≫ Y.hom))
  let K' := (adicUpperStar ℓ T.ι).obj K
  let M := (DerivedCategory.singleFunctor _ 0).obj K'
  have : IsIso (adicRelativeKunnethOpenUnitMap ℓ h j M) :=
    isIso_adicRelativeKunnethOpenUnitMap k₀ ℓ h j K' (hK.upperStar T.ι)
  let eK := (adicUpperStar ℓ a).mapIso ((adicUpperStarComp ℓ α prX).symm.app K) ≪≫
    (adicUpperStarComp ℓ a (α ≫ prX)).symm.app K ≪≫ (adicUpperStarCongr ℓ hp).app K ≪≫
    (adicUpperStarComp ℓ pX T.ι).app K
  let eM := ((adicUpperStar ℓ a).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eK ≪≫
    ((adicUpperStar ℓ pX).mapDerivedCategorySingleFunctor 0).symm.app K'
  have := isIso_adicOpenExtensionPullbackMap ℓ qa
  let ex := (adicOpenImmersionLowerShriek ℓ iX).mapDerivedCategory.mapIso eM.symm ≪≫
    (asIso (adicOpenExtensionPullbackMap ℓ qa.toCommSq)).app L
  refine ⟨(adicUpperStar ℓ pY).mapDerivedCategory.obj
    ((adicLowerStar ℓ h.left).rightDerivedFunctor.obj M), ⟨?_⟩⟩
  exact asIso (adicRelativeKunnethOpenUnitMap ℓ h j M) ≪≫
    (adicLowerStar ℓ (prod.map h (𝟙 D)).left).rightDerivedFunctor.mapIso ex ≪≫
    (adicDerivedBaseChangeIso ℓ q).symm.app _

end WeilII
