module

public import WeilII.Paper.WeakLefschetz
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
import WeilConjectures.TateTwist.LocallyFree
import WeilConjectures.WeilSheaf.Dual
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.OpenComplementVerdierDuality

/-! # An ordinary cohomology criterion for weak Lefschetz -/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits
open scoped CategoryTheory.Obj

universe u

/-- For a lisse sheaf on geometric affine space there is one lisse test sheaf for all
closed immersions. It suffices that its extension by zero have no cohomology below the
middle degree. In Katz A.5 (pp. 220–221) and Zhang, Definition 2.3, this sheaf is the
Tate-twisted dual. Its extension is constructible, so Artin vanishing supplies the degrees
above the middle. Verdier duality and separation by linear forms then give the claim. -/
public theorem exists_lisse_hasWeakLefschetz_of_lower_vanishing
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (n : ℕ) :
    let K := AlgebraicClosure k
    let S := Spec (CommRingCat.of K)
    let X := 𝔸(ULift.{u} (Fin n); S)
    letI : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
    ∀ (G : ProEtale.AdicSheaf ℓ X) (hG : ProEtale.IsAdicLisseSheaf G),
      ∃ L : ProEtale.AdicSheaf ℓ X, ProEtale.IsAdicLisseSheaf L ∧
        ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
          let j := i.openComplement.ι
          let F := (ProEtale.adicOpenImmersionLowerShriek ℓ j).obj
            ((ProEtale.adicUpperStar ℓ j).obj L)
          (∀ r : ℤ, r < n → IsZero ((ProEtale.algClosedCohomology ℓ (X ↘ S) r).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) → HasWeakLefschetz i G hG := by
  classical
  intro K S X G hG
  have hchar : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
  let a := X ↘ S
  have hn : Nat.card (ULift.{u} (Fin n)) = n := by simp
  have : SmoothOfRelativeDimension n a := by
    simpa only [hn] using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) S
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType a
  have : NeZero (ℓ : K) := ⟨fun h ↦ hchar.out
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec K ℓ).1 h)).resolve_left
      CharP.ringChar_ne_one)⟩
  let E := ProEtale.adicSheafEquivCondensedMod ℓ S
  let T := ProEtale.tateTwist S ℓ (n : ℤ)
  have hT : ProEtale.IsAdicConstructibleSheaf (E.inverse.obj T) := by
    have : IsSeparated (Over.mk (𝟙 S)).hom := inferInstanceAs (IsSeparated (𝟙 S))
    have : LocallyOfFiniteType (Over.mk (𝟙 S)).hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
    have : QuasiCompact (Over.mk (𝟙 S)).hom := inferInstanceAs (QuasiCompact (𝟙 S))
    apply (ProEtale.isAdicConstructibleSheaf_iff_isConstructibleModuleObject ℓ k K
      (Over.mk (𝟙 S)) _).mpr
    change ProEtale.IsConstructibleModuleObject (ProEtale.condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) S) (E.functor.obj (E.inverse.obj T))
    exact constructible_of_iso (E.counitIso.app T).symm
      (ProEtale.isLocallyFree_tateTwist ℓ (𝟙 S) n).isConstructibleModuleObject
  let L := (ProEtale.AdicSheaf.ihom G).obj ((ProEtale.adicUpperStar ℓ a).obj (E.inverse.obj T))
  have hL : ProEtale.IsAdicLisseSheaf L := hG.ihom (hT.isAdicLisseSheaf_of_isField.upperStar a)
  refine ⟨L, hL, ?_⟩
  intro Y i _ j F lower e he
  rw [hn] at he
  obtain ⟨D, _⟩ := exists_natural_openComplementVerdierDuality k ℓ a n j e
  have van : IsZero ((ProEtale.algClosedCohomology ℓ a (2 * (n : ℤ) - e)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    rcases lt_or_gt_of_ne he with h | h
    · apply isZero_algClosedCohomology_of_isAffine k ℓ a F
        ((hL.upperStar j).isAdicConstructibleSheaf.openImmersionLowerShriek j) n _ _ (by omega)
      have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension a n
      apply lt_of_le_of_lt hdim
      norm_cast
      omega
    · exact lower _ (by omega)
  have hz := (D G hG).toEquiv.subsingleton_congr.mpr
    (ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat ℓ).map_isZero van))
  have hs := (Module.subsingleton_dual_iff (PadicAlgCl ℓ)).mp hz
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end WeilII
