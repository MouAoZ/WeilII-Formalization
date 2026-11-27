module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom
import WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek
import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison
import WeilII.AlgebraicGeometry.LisseDirectImageVerdierDuality

/-!
# Verdier duality for the direct image from an open complement

Katz, *Affine cohomological transforms, perversity, and monodromy*, proof of Corollary A.5,
pp. 220–221, exchanges compactly supported and ordinary cohomology by duality.
Zhang applies weak Lefschetz to the complex `Rj_* j^* G` in Definition 2.3 and Theorem 2.4.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- For an open immersion into a smooth scheme of pure dimension `d`, the linear dual of
`H_c^e(X, Rj_* j^* G)` is naturally isomorphic to `H^{2d-e}(X, j_! j^*(G^∨(d)))`.
The equality for a morphism of lisse sheaves expresses contravariant naturality in `G`.

Proof. Write `M = j^*G`. The open subscheme is smooth of pure dimension `d` when nonempty,
and `M` is lisse by pullback. The ambient scheme is noetherian, so `j` is quasi-compact and
of finite type. For the empty open both sides vanish. Apply the global Verdier duality
comparison for a direct image from a smooth source to `j` and `M`, as in Katz, proof of A.5,
p. 220. Smooth purity gives the dualizing complex `Q̄ℓ(d)[2d]`. Duality sends `Rj_* M` to
`Rj_!(M^∨(d))[2d]` and compactly supported global sections to ordinary global sections.
Exactness of the vector space dual puts degree `e` in degree `-e`, hence in degree `2d-e`
of the unshifted complex. Write `T` for the pullback to `X` of the geometric Tate line.
Evaluation identifies `G^∨(d)` with the internal Hom from `G` to `T`, as one verifies
on a finite free trivialization. Open restriction commutes with this internal Hom and
with pullback of the Tate line, so `M^∨(d) ≅ j^*(G^∨(d))`. Compactify `j` by following
it with the identity on `X`. This computes `Rj_!` by exact extension by zero and sends
a degree-zero sheaf to its degree-zero extension. The duality comparison and evaluation
are natural, giving the stated equality by precomposition on both duals. -/
public theorem exists_natural_openComplementVerdierDuality
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {X V : Scheme.{u}} (a : X ⟶ Spec (CommRingCat.of (AlgebraicClosure k₀))) (d : ℕ)
    [SmoothOfRelativeDimension d a] [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (j : V ⟶ X) [IsOpenImmersion j] (e : ℤ) :
    let s := Spec (CommRingCat.of (AlgebraicClosure k₀))
    let tateLine := (ProEtale.adicUpperStar ℓ a).obj
      ((ProEtale.adicSheafEquivCondensedMod ℓ s).inverse.obj (ProEtale.tateTwist s ℓ (d : ℤ)))
    let compact := ProEtale.adicUpperStar ℓ j ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      (ProEtale.adicLowerStar ℓ j).rightDerivedFunctor ⋙
      ProEtale.algClosedCompactlySupportedCohomology ℓ a e ⋙ WeilCoefficients.toModuleCat ℓ
    let ordinary := ProEtale.adicUpperStar ℓ j ⋙ ProEtale.adicOpenImmersionLowerShriek ℓ j ⋙
      DerivedCategory.singleFunctor _ 0 ⋙ ProEtale.algClosedCohomology ℓ a (2 * (d : ℤ) - e) ⋙
      WeilCoefficients.toModuleCat ℓ
    ∃ D : ∀ (G : ProEtale.AdicSheaf ℓ X), ProEtale.IsAdicLisseSheaf G →
        Module.Dual (PadicAlgCl ℓ) (compact.obj G) ≃ₗ[PadicAlgCl ℓ]
          ordinary.obj ((ProEtale.AdicSheaf.ihom G).obj tateLine),
      ∀ {G G' : ProEtale.AdicSheaf ℓ X} (hG : ProEtale.IsAdicLisseSheaf G)
        (hG' : ProEtale.IsAdicLisseSheaf G') (f : G ⟶ G')
        (φ : Module.Dual (PadicAlgCl ℓ) (compact.obj G')),
        D G hG (φ.comp (compact.map f).hom) =
          ordinary.map ((Mod.ihomMap f).app tateLine) (D G' hG' φ) := by
  intro s tateLine compact ordinary
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType a
  have : SmoothOfRelativeDimension d (j ≫ a) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d j a
  obtain ⟨D, natural⟩ := exists_natural_lisseDirectImageVerdierDuality k₀ ℓ a j d
    (.ofIsOpenImmersion j) e
  let J := ProEtale.adicUpperStar ℓ j
  let E := ProEtale.adicOpenImmersionLowerShriek ℓ j
  let H := ProEtale.algClosedCohomology ℓ a (2 * (d : ℤ) - e) ⋙ WeilCoefficients.toModuleCat ℓ
  let T := (ProEtale.adicSheafEquivCondensedMod ℓ s).inverse.obj (ProEtale.tateTwist s ℓ (d : ℤ))
  let Tᵥ := (ProEtale.adicUpperStar ℓ (j ≫ a)).obj T
  let line : Tᵥ ≅ J.obj tateLine := (ProEtale.adicUpperStarComp ℓ j a).app T
  let coeff (G : ProEtale.AdicSheaf ℓ X) :
      J.obj ((ProEtale.AdicSheaf.ihom G).obj tateLine) ≅
        (ProEtale.AdicSheaf.ihom (J.obj G)).obj Tᵥ :=
    asIso (ProEtale.adicUpperStarIhomComparison ℓ j G tateLine) ≪≫
      (ProEtale.AdicSheaf.ihom (J.obj G)).mapIso line.symm
  let R := (ProEtale.adicLowerStar ℓ (𝟙 X)).rightDerivedFunctor
  let rid : R ≅ 𝟭 _ := Functor.rightDerivedFunctorNatIso (ProEtale.adicLowerStarId ℓ X) ≪≫
    (𝟭 (ProEtale.AdicSheaf ℓ X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso _
  let F := DerivedCategory.singleFunctor _ 0 ⋙ E.mapDerivedCategory ⋙ R ⋙ H
  let F₀ := E ⋙ DerivedCategory.singleFunctor _ 0 ⋙ H
  let shrink : F ≅ F₀ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ E.mapDerivedCategory) rid ≪≫
      Functor.rightUnitor _ ≪≫ E.mapDerivedCategorySingleFunctor 0) H
  let rightIso (G : ProEtale.AdicSheaf ℓ X) :=
    shrink.app ((ProEtale.AdicSheaf.ihom (J.obj G)).obj Tᵥ) ≪≫ F₀.mapIso (coeff G).symm
  refine ⟨fun G hG ↦ (D (J.obj G) (hG.upperStar j)).trans (rightIso G).toLinearEquiv, ?_⟩
  intro G G' hG hG' f φ
  have forward : J.map ((Mod.ihomMap f).app tateLine) ≫ (coeff G).hom =
      (coeff G').hom ≫ (Mod.ihomMap (J.map f)).app Tᵥ := by
    dsimp only [coeff, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ProEtale.adicUpperStarIhomComparison_ihomMap, Category.assoc,
      Category.assoc, (Mod.ihomMap (J.map f)).naturality line.inv]
  have backward : (Mod.ihomMap (J.map f)).app Tᵥ ≫ (coeff G).inv =
      (coeff G').inv ≫ J.map ((Mod.ihomMap f).app tateLine) := by
    apply (cancel_epi (coeff G').hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← forward, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have square : F.map ((Mod.ihomMap (J.map f)).app Tᵥ) ≫ (rightIso G).hom =
      (rightIso G').hom ≫ F₀.map (J.map ((Mod.ihomMap f).app tateLine)) := by
    dsimp only [rightIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, shrink.hom.naturality, Category.assoc, ← F₀.map_comp, backward,
      F₀.map_comp, Category.assoc]
  exact (congrArg (fun x : F.obj ((ProEtale.AdicSheaf.ihom (J.obj G)).obj Tᵥ) ↦
      (rightIso G).hom x) (natural (hG.upperStar j) (hG'.upperStar j) (J.map f) φ)).trans
    (ConcreteCategory.congr_hom square (D (J.obj G') (hG'.upperStar j) φ))

end WeilII
