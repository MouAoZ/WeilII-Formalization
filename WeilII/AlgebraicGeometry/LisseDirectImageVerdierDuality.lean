module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilII.HomologicalAlgebra.LinearDualNaturality
import WeilII.AlgebraicGeometry.BoundedConstructibleAdicRealization
import WeilII.AlgebraicGeometry.BoundedVerdierDirectImage
import WeilII.AlgebraicGeometry.GeometricPointCohomologyLinearDual
import WeilII.AlgebraicGeometry.LisseDerivedHomIntoTateLine
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.PoincareDuality.Biduality.Constructible
import WeilConjectures.PoincareDuality.Poincare
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!
# Verdier duality for the direct image of a lisse sheaf

Katz, *Affine cohomological transforms, perversity, and monodromy*, A.5–A.6, pp. 220–221,
uses Verdier duality to exchange compactly supported cohomology of an ordinary direct image
with ordinary cohomology of an exceptional direct image. The shift and twist come from
the smooth source. See also SGA 4 XVIII, 3.1.10 and 3.2.5–3.2.6, and SGA 4½,
*Théorèmes de finitude*, §§4.2–4.4.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Let `g : V ⟶ B` be a morphism of separated finite-type schemes over a geometric point,
with `V` smooth of pure dimension `d`. For every finite-rank lisse sheaf `M`, the linear dual
of `H_c^r(B, Rg_* M)` is naturally isomorphic to `H^{2d-r}(B, Rg_! (M^∨(d)))`.
The compactification `c` computes `Rg_!` by extension by zero followed by proper direct image.

Proof (Katz, A.5–A.6, pp. 220–221). Write `a` for the structure morphism of `B` and `b = g ≫ a`.
Both schemes are noetherian. Factoring `g` as its closed graph followed by the base change of
`b` shows that `g` is separated of finite type. The lisse sheaf in degree zero is bounded
constructible, and so is its derived direct image. Pass to the equivalent condensed model,
writing `K` for the image of this sheaf and `C = Rg_* K`. For each structure morphism `a_Z`
put `ω_Z = a_Z^! 1` and `D_Z = RHom(-, ω_Z)`. Composition gives `g^! ω_B ≅ ω_V`.
Relative Verdier exchange gives `Rg_* D_V L ≅ D_B Rg_! L`. Apply this to `L = D_V K` and
use biduality for `K` to get `C ≅ D_B T`, where `T = Rg_! D_V K`. Applying `D_B` and using
biduality for the bounded constructible object `T` gives `D_B C ≅ T`.

Smooth purity identifies `ω_V` with the Tate line of twist `d`, shifted by `2d`. On a finite
free trivialization of `M`, its derived internal Hom into this line is the ordinary internal
Hom in degree zero. Evaluation glues these identifications, so `D_V K` is the image of
`M^∨(d)[2d]`. Apply Verdier exchange to `a` with coefficient the unit on the geometric point
to identify `RHom(Ra_! C, 1)` with `Ra_* D_B C`. On the point, cohomology in degree `-r` of
this internal dual is the linear dual of cohomology in degree `r` of `Ra_! C`, by the
geometric-point comparison and exactness of duality on finite-dimensional vector spaces.
Transport the ordinary and exceptional direct images back to the adic model, computing each
exceptional image with the same compactification on both sides of the model comparison.
Independence of compactification identifies any other choices. The shift on the right puts
degree `-r` in degree `2d-r`. All comparisons are natural and linear. For a morphism `M ⟶ M'`,
the dual on the left and the internal Hom on the right both act by precomposition. -/
public theorem exists_natural_lisseDirectImageVerdierDuality
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {V B : Scheme.{u}} (a : B ⟶ Spec (CommRingCat.of (AlgebraicClosure k₀)))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] (g : V ⟶ B) (d : ℕ)
    [SmoothOfRelativeDimension d (g ≫ a)] [IsSeparated (g ≫ a)] [QuasiCompact (g ≫ a)]
    (c : Compactification g) (r : ℤ) :
    let s := Spec (CommRingCat.of (AlgebraicClosure k₀))
    let tateLine := (ProEtale.adicUpperStar ℓ (g ≫ a)).obj
      ((ProEtale.adicSheafEquivCondensedMod ℓ s).inverse.obj (ProEtale.tateTwist s ℓ (d : ℤ)))
    let compact := DerivedCategory.singleFunctor _ 0 ⋙
      (ProEtale.adicLowerStar ℓ g).rightDerivedFunctor ⋙
      ProEtale.algClosedCompactlySupportedCohomology ℓ a r ⋙ WeilCoefficients.toModuleCat ℓ
    let ordinary := DerivedCategory.singleFunctor _ 0 ⋙
      (ProEtale.adicOpenImmersionLowerShriek ℓ c.i).mapDerivedCategory ⋙
      (ProEtale.adicLowerStar ℓ c.g).rightDerivedFunctor ⋙
      ProEtale.algClosedCohomology ℓ a (2 * (d : ℤ) - r) ⋙ WeilCoefficients.toModuleCat ℓ
    ∃ D : ∀ (M : ProEtale.AdicSheaf ℓ V), ProEtale.IsAdicLisseSheaf M →
        Module.Dual (PadicAlgCl ℓ) (compact.obj M) ≃ₗ[PadicAlgCl ℓ]
          ordinary.obj ((ProEtale.AdicSheaf.ihom M).obj tateLine),
      ∀ {M M' : ProEtale.AdicSheaf ℓ V} (hM : ProEtale.IsAdicLisseSheaf M)
        (hM' : ProEtale.IsAdicLisseSheaf M') (f : M ⟶ M')
        (φ : Module.Dual (PadicAlgCl ℓ) (compact.obj M')),
        D M hM (φ.comp (compact.map f).hom) =
          ordinary.map ((Mod.ihomMap f).app tateLine) (D M' hM' φ) :=
  open scoped CategoryTheory.Obj in
  open ProEtale ProEtale.CondensedRing Opposite MonoidalCategory in by
  classical
  intro s tateLine compact ordinary
  have : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
    ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ CharP.prime_ringChar k₀⟩
  have : Fact (ringChar (AlgebraicClosure k₀) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
  let X := Over.mk (g ≫ a)
  let Y := Over.mk a
  let p := point (AlgebraicClosure k₀)
  let f : X ⟶ Y := Over.homMk g rfl
  let b : Y ⟶ p := Over.homMk a (by simp [Y, p])
  have hb : b = Over.mkIdTerminal.from Y := Over.mkIdTerminal.hom_ext _ _
  have := SmoothOfRelativeDimension.smooth d (g ≫ a)
  have : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (g ≫ a))
  have : IsSeparated X.hom := inferInstanceAs (IsSeparated (g ≫ a))
  have : QuasiCompact X.hom := inferInstanceAs (QuasiCompact (g ≫ a))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType a)
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated a)
  have : QuasiCompact Y.hom := inferInstanceAs (QuasiCompact a)
  have : SmoothOfRelativeDimension d (Over.mkIdTerminal.from X).left := by
    rw [Over.mkIdTerminal_from_left]
    exact inferInstanceAs (SmoothOfRelativeDimension d (g ≫ a))
  let t : ℤ := 2 * (d : ℤ)
  let ι := (adicLisseSheaf ℓ V).ι
  let A := ι ⋙ DerivedCategory.singleFunctor _ 0
  let H := ProEtaleWeilSheaf.ordinaryIhomBifunctor ℓ V
  let A' := ι.op ⋙ H.flip.obj tateLine ⋙ DerivedCategory.singleFunctor _ 0
  let E := adicSheafDerivedEquivCondensedMod ℓ V
  obtain ⟨hK, hN, ⟨elisse⟩⟩ := nonempty_lisseDerivedHomIntoTateLineIso k₀ ℓ X (d : ℤ) t
  let K := ObjectProperty.lift _ (A ⋙ E.functor) hK
  let N := ObjectProperty.lift _ (A' ⋙ E.functor ⋙ shiftFunctor _ t) hN
  let DX := (boundedConstructibleHom ℓ X).flip.obj (dualizingComplex ℓ X)
  let eV : K.op ⋙ DX ≅ N :=
    Functor.isoWhiskerLeft K.op ((boundedConstructibleHom ℓ X).flip.mapIso
      (boundedConstructibleSmoothPurityIso ℓ (Over.mkIdTerminal.from X) d)) ≪≫ elisse
  let G := boundedConstructibleLowerStar ℓ f
  let P := boundedConstructibleLowerShriek ℓ f
  let Bstar := boundedConstructibleLowerStar ℓ b
  let Bshriek := boundedConstructibleLowerShriek ℓ b
  let C := K ⋙ G ⋙ Bshriek
  let O := N ⋙ P ⋙ Bstar
  let U := ObjectProperty.FullSubcategory.mk _ (boundedConstructible_tensorUnit
    (Profinite.padicAlgClRingObj ℓ) s)
  let D := (boundedConstructibleHom ℓ p).flip.obj U
  let eω : (boundedConstructibleUpperShriek ℓ b).obj U ≅ dualizingComplex ℓ Y :=
    eqToIso (by rw [hb]; rfl)
  let eGeom : C.op ⋙ D ≅ O :=
    Functor.isoWhiskerLeft (K ⋙ G).op (boundedVerdierExchangeIso ℓ b U).symm ≪≫
    Functor.isoWhiskerLeft (K ⋙ G).op (Functor.isoWhiskerRight
      ((boundedConstructibleHom ℓ Y).flip.mapIso eω) Bstar) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft K.op (boundedVerdierStarDualIso ℓ f)) Bstar ≪≫
    Functor.isoWhiskerRight eV (P ⋙ Bstar)
  let Γ := (adicGlobalSections ℓ s).rightDerivedFunctor
  let fiber (i : ℤ) := boundedAdicRealization ℓ s ⋙ Γ ⋙ DerivedCategory.homologyFunctor _ i ⋙
    WeilCoefficients.toModuleCat ℓ
  let gs := (adicLowerStar ℓ g).rightDerivedFunctor
  let ac := HasCompactification.compactification a
  let ash := (adicOpenImmersionLowerShriek ℓ ac.i).mapDerivedCategory ⋙
    (adicLowerStar ℓ ac.g).rightDerivedFunctor
  let eK : K ⋙ boundedAdicRealization ℓ V ≅ A := Functor.isoWhiskerLeft A E.unitIso.symm
  let ec : C ⋙ boundedAdicRealization ℓ s ≅ A ⋙ gs ⋙ ash :=
    Functor.isoWhiskerLeft (K ⋙ G) (boundedShriekAdicRealizationIso ℓ b ac) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft K (boundedStarAdicRealizationIso ℓ f)) ash ≪≫
    Functor.isoWhiskerRight eK (gs ⋙ ash)
  let ecH : C ⋙ fiber r ≅ ι ⋙ compact :=
    Functor.isoWhiskerRight ec (Γ ⋙ DerivedCategory.homologyFunctor _ r ⋙ WeilCoefficients.toModuleCat ℓ)
  let gsh := (adicOpenImmersionLowerShriek ℓ c.i).mapDerivedCategory ⋙
    (adicLowerStar ℓ c.g).rightDerivedFunctor
  let ast := (adicLowerStar ℓ a).rightDerivedFunctor
  let eN : N ⋙ boundedAdicRealization ℓ V ≅ A' ⋙ shiftFunctor _ t :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft A' (E.functor.commShiftIso t).symm) E.inverse ≪≫
    Functor.isoWhiskerLeft (A' ⋙ shiftFunctor _ t) E.unitIso.symm
  let eo : O ⋙ boundedAdicRealization ℓ s ⋙ Γ ≅ A' ⋙ gsh ⋙ ast ⋙ Γ ⋙ shiftFunctor _ t :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (N ⋙ P) (boundedStarAdicRealizationIso ℓ b) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft N (boundedShriekAdicRealizationIso ℓ f c)) ast)
      Γ ≪≫
    Functor.isoWhiskerRight eN (gsh ⋙ ast ⋙ Γ) ≪≫
    Functor.isoWhiskerLeft A' ((gsh ⋙ ast ⋙ Γ).commShiftIso t)
  let Q := ι.op ⋙ H.flip.obj tateLine
  let eoH : C.op ⋙ D ⋙ fiber (-r) ≅ Q ⋙ ordinary :=
    Functor.isoWhiskerRight eGeom (fiber (-r)) ≪≫
    Functor.isoWhiskerRight eo (DerivedCategory.homologyFunctor _ (-r) ⋙ WeilCoefficients.toModuleCat ℓ) ≪≫
    Functor.isoWhiskerLeft (A' ⋙ gsh ⋙ ast ⋙ Γ) (Functor.isoWhiskerRight
      ((DerivedCategory.homologyFunctor _ 0).shiftIso t (-r) (t - r) (by omega))
      (WeilCoefficients.toModuleCat ℓ))
  obtain ⟨ep, hp⟩ := exists_natural_geometricPointCohomologyLinearDual k₀ ℓ r
  obtain ⟨e, he⟩ := exists_natural_linearDual_of_iso C (fiber r) (D ⋙ fiber (-r))
    ecH eoH ep hp
  refine ⟨fun M hM ↦ e ⟨M, hM⟩, ?_⟩
  intro M M' hM hM' j φ
  exact he (M := ⟨M, hM⟩) (M' := ⟨M', hM'⟩) (ObjectProperty.homMk j) φ

end WeilII
