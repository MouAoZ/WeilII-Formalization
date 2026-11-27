module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilII.AlgebraicGeometry.AdicOpenExtensionDirectImageExchange
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilII.AlgebraicGeometry.AdicGenericFiberDirectImageBaseChange
import WeilII.AlgebraicGeometry.AdicOpenExchangeSpecialization
import WeilII.AlgebraicGeometry.ProjectiveSpaceIntegral
import WeilII.Paper.KatzUniversalHyperplaneExtensionByZeroExchange

/-!
# Extension by zero and direct image on a generic hyperplane complement

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.3,
pp. 219–220, specialized to a constructible sheaf in degree zero.
-/

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

universe u

/-- Katz, Lemma A.3, pp. 219–220. For a fixed constructible sheaf `K`, the canonical map
`β_! Rg_* M ⟶ Rf_* j_! M` is invertible for every hyperplane in one dense open of the dual
projective space. Here `β : B ↪ P` includes the hyperplane complement, `j : f⁻¹B ↪ X`,
`g : f⁻¹B ⟶ B` is the restriction of `f`, and `M = (j^*K)[0]`.

Proof. Let `D` be the dual projective space, `F = f × id_D`, and `β̃` the open complement of
the incidence subscheme in `P × D`. Write `α` for the inverse image open in `X × D` and `G`
for the restriction of `F` to this open. Put `A = α^* pr_X^* K` and `L = A[0]`.
Katz A.2 gives an invertible adjunction map `e : β̃_! RG_* L ⟶ RF_* α_! L`.

The sheaf `A` is constructible by pullback. The schemes are of finite type over a field,
so the open immersion `α` is quasi-compact. Consequently `α_! A` is constructible, and
exactness of extension by zero identifies `α_! L` with `(α_! A)[0]`. The morphisms `F`
and `G` are separated of finite type by base change. Apply generic base change over the
integral projective space `D` to `(G,A)` and `(F,α_! A)`, as in Katz's application of
SGA 4½, *Théorèmes de finitude* 1.9. Intersect the two dense opens.

For each parameter in their intersection, the fibre of the incidence equation is the chosen
hyperplane, and the restriction of `L` to its open complement on `X` is `M`. Commuting
pullback with `β̃_!` and then with `RG_*` identifies the source of the fibre of `e` with
`β_! Rg_* M`. Commuting pullback with `RF_*` and then with `α_!` identifies the target
with `Rf_* j_! M`. All four comparisons are invertible on this open.

Under these identifications the fibre of `e` is the stated map. Indeed, transpose under
`f^* ⊣ Rf_*`. The base-change map for `F` transposes to the pullback of its counit, so
composing with the fibre of `e` gives the pullback of the transpose of `e`. On the source
side, pulling back the base-change map for `G` along `g` and composing with the counit
for `g` gives the restriction of the counit for `G`. Naturality of open-extension pullback
on this counit and its compatibility with pasting identify the two transposes. Adjunction
then identifies the maps. The fibre of the isomorphism `e` is invertible. -/
public theorem exists_denseOpen_isIso_hyperplaneExtensionByZeroExchange
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (I : Type u) [Fintype I] [Nontrivial I] {X : Scheme.{u}} :
    let k := AlgebraicClosure k₀
    let S := Spec (CommRingCat.of k)
    let P := ℙ(I; S)
    letI : S.Over S := ⟨𝟙 S⟩
    ∀ [X.Over S] (f : X ⟶ P) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f] (K : AdicSheaf ℓ X), IsAdicConstructibleSheaf K →
      ∃ W : P.Opens, Dense (W : Set P) ∧
        ∀ (H : S ⟶ P) [H.IsOver S], H (IsLocalRing.closedPoint k) ∈ W →
          let B := (projectiveHyperplaneFiber H).subschemeι.openComplement
          let M := (DerivedCategory.singleFunctor _ 0).obj ((adicUpperStar ℓ (f ⁻¹ᵁ B).ι).obj K)
          IsIso ((adicOpenExtensionDirectImageExchange ℓ f B).app M) := by
  classical
  intro k S P instX f hf hsep hft hqc K hK
  let π := P ↘ S
  let p := Limits.pullback.snd π π
  let pr := Limits.pullback.fst (f ≫ π) π
  let F := Limits.pullback.map (f ≫ π) π π π f (𝟙 P) (𝟙 S) (by simp) (by simp)
  have prodSq : IsPullback pr F f (Limits.pullback.fst π π) := by
    apply IsPullback.of_bot _ (by simp [pr, F]) (IsPullback.of_hasPullback π π)
    simpa [F, pr] using IsPullback.of_hasPullback (f ≫ π) π
  have : IsSeparated F := MorphismProperty.of_isPullback prodSq hsep
  have : LocallyOfFiniteType F := MorphismProperty.of_isPullback prodSq hft
  have : QuasiCompact F := MorphismProperty.of_isPullback prodSq hqc
  have : IsIntegral P := isIntegral_projectiveSpace_over_field I k
  have : IsNoetherian (Limits.pullback (f ≫ π) π) :=
    isNoetherian_of_locallyOfFiniteType (pr ≫ f ≫ π)
  let B := (projectiveHyperplaneIncidenceFamily I S).subschemeι.openComplement
  let α := (F ⁻¹ᵁ B).ι
  let A := (adicUpperStar ℓ α).obj ((adicUpperStar ℓ pr).obj K)
  let L := (DerivedCategory.singleFunctor _ 0).obj A
  let extA := adicOpenImmersionLowerShriek ℓ α
  have hA : IsAdicConstructibleSheaf A := (hK.upperStar pr).upperStar α
  have hL : IsIso ((adicOpenExtensionDirectImageExchange ℓ F B).app L) :=
    isIso_universalHyperplaneExtensionByZeroExchange k₀ ℓ I f K hK
  obtain ⟨W, hW, bc⟩ := exists_denseOpen_isIso_adicDerivedBaseChange_onFibers k₀ ℓ π p F
    (extA.obj A) (hA.openImmersionLowerShriek α)
  refine ⟨W, hW, ?_⟩
  intro H hH hHW
  let : S.Over S := ⟨𝟙 S⟩
  have secH : H ≫ π = 𝟙 S := comp_over H S
  let y := Limits.pullback.lift (𝟙 P) (π ≫ H) (by simp [secH] : 𝟙 P ≫ π = (π ≫ H) ≫ π)
  let x := Limits.pullback.lift (𝟙 X) ((f ≫ π) ≫ H)
    (by simp [secH] : 𝟙 X ≫ (f ≫ π) = ((f ≫ π) ≫ H) ≫ π)
  have ySq : IsPullback y π p H := by
    apply IsPullback.of_right _ (Limits.pullback.lift_snd ..) (IsPullback.of_hasPullback π π)
    simpa only [y, Limits.pullback.lift_fst, secH] using IsPullback.of_id_fst (f := π)
  have q : IsPullback x f F y := by
    apply IsPullback.of_right _ _ prodSq
    · simpa only [x, pr, y, Limits.pullback.lift_fst] using IsPullback.of_id_fst (f := f)
    · apply Limits.pullback.hom_ext <;> simp [F, x, y]
  have hbc := bc H secH hHW ySq q
  have hF : IsIso ((adicDerivedBaseChange ℓ q.toCommSq).app (extA.mapDerivedCategory.obj L)) :=
    (NatTrans.isIso_app_iff_of_iso _ ((extA.mapDerivedCategorySingleFunctor 0).app A)).2 hbc
  have hB : (projectiveHyperplaneFiber H).subschemeι.openComplement = y ⁻¹ᵁ B := by
    ext z
    change z ∉ Set.range _ ↔ y z ∉ Set.range _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι,
      projectiveHyperplaneFiber, Scheme.IdealSheafData.coe_support_comap]
    rfl
  dsimp only
  rw [hB]
  let V := f ⁻¹ᵁ (y ⁻¹ᵁ B)
  have hV : V = x ⁻¹ᵁ (F ⁻¹ᵁ B) := by
    change f ⁻¹ᵁ (y ⁻¹ᵁ B) = _
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, q.w]
  let a := x.resLE (F ⁻¹ᵁ B) V hV.le
  have qa : IsPullback a V.ι α x := IsOpenImmersion.isPullback _ _ _ _
    (x.resLE_comp_ι hV.le).symm (by simpa [α] using hV.symm)
  have hx : x ≫ pr = 𝟙 X := Limits.pullback.lift_fst ..
  let ex := (adicUpperStarComp ℓ x pr).symm.app K ≪≫
    (adicUpperStarCongr ℓ hx).app K ≪≫ (adicUpperStarId ℓ X).app K
  let ea := (adicUpperStarCompIso ℓ qa.w).app ((adicUpperStar ℓ pr).obj K) ≪≫
    (adicUpperStar ℓ V.ι).mapIso ex
  let e := ((adicUpperStar ℓ a).mapDerivedCategorySingleFunctor 0).app A ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ea
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 (isIso_adicOpenExchange_of_baseChange ℓ q.toCommSq
    B (y ⁻¹ᵁ B) (isPullback_morphismRestrict y B) qa L hL hF)

end WeilII
