module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilII.Paper.ChainSectionPolynomial
public import WeilII.Paper.WeakLefschetz
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek
import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.LisseDirectImageVerdierDuality
import WeilII.AlgebraicGeometry.OpenComplementVerdierDuality
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.TateTwist.LocallyFree
import WeilConjectures.WeilSheaf.Dual
import WeilII.AlgebraicGeometry.AffineCompactificationCohomology
import WeilII.Paper.ChainGraphIncidenceCompactification
import WeilII.Paper.KatzGenericHyperplaneCohomologyComparison

/-!
# Weak Lefschetz on a principal open of chain sections

This is the geometric vanishing used in Zhang, *On an elementary proof of Weil II*,
Definition 2.3 and Construction 2.5, p. 3. The proof applies Katz's hyperplane comparison
to the graph of the chain quadratic.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory

universe u

/-- For each geometric lisse sheaf, the chain sections of Zhang's Construction 2.5 satisfy
Definition 2.3 throughout a nonempty principal open of the normalized parameter chart.
The first `n` parameters give the linear coefficients and the last gives the constant.

Proof. Write `K` for the algebraic closure of `k`, `X = 𝔸ⁿ_K`, and `Q` for the chain
quadratic. The map `f(x) = [1 : x : Q(x)]` is a closed graph in a standard affine chart
followed by its open immersion, hence separated of finite type. The sheaf `L = Gᵛ(n)` is
lisse by local trivialization and therefore constructible. Katz, *Affine cohomological
transforms, perversity, and monodromy*, A.4, gives a dense open of hyperplanes for `(f,L)`
on which the comparison holds in every degree. It meets the chart where the coefficient of
the last coordinate is one after normalization. Inside this intersection choose a nonempty
principal open `D(g)` using the principal open basis of affine space. Thus `g ≠ 0`.

At a point of `D(g)`, the hyperplane equation pulls back to `P = Q + a·x + c`. Write
`j : V = D(P) ↪ X` for the open complement and `M = j^*L`. Given an integer `e ≠ n`,
put `r = 2n − e`. Since `X` is smooth of pure dimension `n`, open-complement Verdier
duality identifies the dual of `H_c^e(X, Rj_*j^*G)` with `H^r(X, j_!M)`. If `e < n`,
then `r > n`. Exact extension by zero gives a constructible sheaf in degree zero, lisse
on `V` and zero on its complement. The affine cohomological dimension bound on `X` gives
vanishing (SGA 4, XIV, 3.1, in its geometric adic form).

If `e > n`, Katz A.4 identifies the ordinary group with `H_c^r(B, Rh_*M)`, where `B` is
the hyperplane complement and `h : V → B` is the restricted graph. In affine coordinates
on `B`, the image is the open `t ≠ 0` of the hypersurface `Z` cut out by
`t(1 − a·v − ct) − Q(v)`. Indeed `(t,v) = (1/P,x/P)` and the inverse is `x = v/t`.
The equation has linear term `t`, so every prime chain in its zero locus extends strictly
by the zero prime in the polynomial ring. Hence `dim Z ≤ n`. Write `h` as the resulting
open immersion `w : V ↪ Z` followed by the closed immersion `b : Z ↪ B`.

The source `V` is smooth of pure dimension `n`, and `b` is proper. Direct-image duality
using this compactification identifies the dual of `H_c^r(B, Rh_*M)` with
`H^e(B, Rb_*w_!(Mᵛ(n)))`, since `2n − r = e` (Katz A.5–A.6). Composition of ordinary
direct images computes this as `H^e(Z, w_!(Mᵛ(n)))`. Again the extension by zero is a
constructible sheaf in degree zero. The affine bound on `Z` gives zero since `e > n ≥ dim Z`.
Linear duals over the coefficient field detect zero. Applying this to the duality
identifications gives the asserted vanishing for every `e ≠ n` on the chosen open. -/
public theorem exists_chainSection_basicOpen_hasWeakLefschetz
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (n : ℕ) (hn : 2 ≤ n) :
    let K := AlgebraicClosure k
    let S := Spec (CommRingCat.of K)
    let X := 𝔸(ULift.{u} (Fin n); S)
    letI : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
    ∀ (G : ProEtale.AdicSheaf ℓ X) (hG : ProEtale.IsAdicLisseSheaf G),
      ∃ g : MvPolynomial (Fin (n + 1)) K, g ≠ 0 ∧
        ∀ (a : Fin n → K) (c : K), MvPolynomial.eval (Fin.snoc a c) g ≠ 0 →
          let coeff := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (X ↘ S).appTop).hom
          let p := MvPolynomial.eval₂Hom coeff
            (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i)) (chainSectionPolynomial a c)
          HasWeakLefschetz (X.zeroLocusSubschemeι {p}) G hG := open CategoryTheory.Limits in by
  classical
  intro K S X G hG
  let : S.Over S := ⟨𝟙 S⟩
  let J := ULift.{u} (Fin (n + 2))
  let P := ℙ(J; S)
  let s := X ↘ S
  let π := P ↘ S
  have hn' : Nat.card (ULift.{u} (Fin n)) = n := by simp
  have : SmoothOfRelativeDimension n s := by
    simpa only [hn'] using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) S
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType s
  have : IsNoetherian P := isNoetherian_of_locallyOfFiniteType π
  have hchar : ringChar K ≠ ℓ := Algebra.ringChar_eq k K ▸ Fact.out
  have : NeZero (ℓ : K) := ⟨fun h ↦ hchar
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec K ℓ).1 h)).resolve_left
      CharP.ringChar_ne_one)⟩
  let E := ProEtale.adicSheafEquivCondensedMod ℓ S
  let T := E.inverse.obj (ProEtale.tateTwist S ℓ (n : ℤ))
  have hT : ProEtale.IsAdicLisseSheaf T := by
    let : MonObj (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) S) :=
      (ProEtale.upperStarFromPoint S).monObjObj (Profinite.padicAlgClRingObj ℓ)
    have : IsSeparated (Over.mk (𝟙 S)).hom := inferInstanceAs (IsSeparated (𝟙 S))
    have : LocallyOfFiniteType (Over.mk (𝟙 S)).hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
    have : QuasiCompact (Over.mk (𝟙 S)).hom := inferInstanceAs (QuasiCompact (𝟙 S))
    apply ProEtale.IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isField
    apply (ProEtale.isAdicConstructibleSheaf_iff_isConstructibleModuleObject ℓ k K
      (Over.mk (𝟙 S)) T).mpr
    change ProEtale.IsConstructibleModuleObject (ProEtale.condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) S) (E.functor.obj T)
    exact constructible_of_iso (E.counitIso.app _).symm
      (ProEtale.isLocallyFree_tateTwist ℓ (𝟙 S) n).isConstructibleModuleObject
  let L := (ProEtale.AdicSheaf.ihom G).obj ((ProEtale.adicUpperStar ℓ s).obj T)
  have hL : ProEtale.IsAdicLisseSheaf L := hG.ihom (hT.upperStar s)
  obtain ⟨f, hf, chart⟩ := exists_chainGraph_incidenceCompactification K n hn
  have hbase : f ≫ π = s := comp_over f S
  have : IsSeparated (f ≫ π) := by rw [hbase]; infer_instance
  have : LocallyOfFiniteType (f ≫ π) := by rw [hbase]; infer_instance
  have : QuasiCompact (f ≫ π) := by rw [hbase]; infer_instance
  have : IsSeparated f := IsSeparated.of_comp f π
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f π
  have : QuasiCompact f := QuasiCompact.of_comp f π
  obtain ⟨compare, generic⟩ := exists_denseOpen_isIso_hyperplaneCohomologyComparison k ℓ J f
  have hK := hL.isAdicConstructibleSheaf
  obtain ⟨W, hW, isoOn⟩ := generic L hK
  obtain ⟨g, hg, params⟩ := chart W hW
  refine ⟨g, hg, ?_⟩
  intro a c hac coeff p
  obtain ⟨H, hH, hHW, hpre, C, haff, hdim⟩ := params a c hac
  let B := (projectiveHyperplaneFiber H).subschemeι.openComplement
  let j := (f ⁻¹ᵁ B).ι
  let h := morphismRestrict f B
  let b := B.ι ≫ π
  let M := (ProEtale.adicUpperStar ℓ j).obj L
  let F := (ProEtale.adicOpenImmersionLowerShriek ℓ j).obj M
  have hM : ProEtale.IsAdicLisseSheaf M := hL.upperStar j
  have hb : h ≫ b = j ≫ s := by
    change (f ∣_ B) ≫ B.ι ≫ π = _
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hbase]
  have : SmoothOfRelativeDimension n (h ≫ b) := by
    rw [hb]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n j s
  have : IsSeparated (h ≫ b) := by rw [hb]; infer_instance
  have : QuasiCompact (h ≫ b) := by rw [hb]; infer_instance
  intro e he
  rw [hn'] at he
  let compact (U : X.Opens) := (ProEtale.algClosedCompactlySupportedCohomology ℓ s e).obj
    ((ProEtale.adicLowerStar ℓ U.ι).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj ((ProEtale.adicUpperStar ℓ U.ι).obj G)))
  change IsZero (compact (X.zeroLocusSubschemeι {p}).openComplement)
  rw [← hpre]
  let r := 2 * (n : ℤ) - e
  obtain ⟨D, _⟩ := exists_natural_openComplementVerdierDuality k ℓ s n j e
  have ordinary : IsZero ((ProEtale.algClosedCohomology ℓ s r).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    rcases lt_or_gt_of_ne he with below | above
    · apply isZero_algClosedCohomology_of_isAffine k ℓ s F
        (hM.isAdicConstructibleSheaf.openImmersionLowerShriek j) n _ _ (by dsimp [r]; omega)
      apply lt_of_le_of_lt (topologicalKrullDim_le_of_smoothOfRelativeDimension s n)
      norm_cast
      omega
    · let N := (ProEtale.AdicSheaf.ihom M).obj ((ProEtale.adicUpperStar ℓ (h ≫ b)).obj T)
      have hN : ProEtale.IsAdicConstructibleSheaf N :=
        (hM.ihom (hT.upperStar (h ≫ b))).isAdicConstructibleSheaf
      have hz := isZero_cohomology_shriek_of_affineCompactification k ℓ b h C n hdim N hN
        (2 * (n : ℤ) - r) (by dsimp [r]; omega)
      obtain ⟨D', _⟩ := exists_natural_lisseDirectImageVerdierDuality k ℓ b h n C r
      have hdual := (D' M hM).toEquiv.subsingleton_congr.mpr
        (ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat ℓ).map_isZero hz))
      have hs := (Module.subsingleton_dual_iff (PadicAlgCl ℓ)).mp hdual
      have hc : IsZero ((ProEtale.algClosedCompactlySupportedCohomology ℓ b r).obj
          ((ProEtale.adicLowerStar ℓ h).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := ModuleCat.isZero_iff_subsingleton.mpr hs
      have := isoOn H hHW r
      exact hc.of_iso (asIso ((compare H r).app ⟨L, hK⟩)).symm
  have dual := (D G hG).toEquiv.subsingleton_congr.mpr
    (ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat ℓ).map_isZero ordinary))
  have hs := (Module.subsingleton_dual_iff (PadicAlgCl ℓ)).mp dual
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end WeilII
