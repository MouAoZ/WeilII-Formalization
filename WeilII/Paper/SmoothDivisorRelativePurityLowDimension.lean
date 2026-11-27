module

public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.Tensor
import WeilConjectures.WeilSheaf.HomotopyInvariance.Basic
import WeilII.AlgebraicGeometry.LisseClosedPurityOfConstant
import WeilII.AlgebraicGeometry.SmoothClosedConstantOrientation
import WeilII.AlgebraicGeometry.SmoothRegularImmersionDimension

/-!
# Relative purity for a smooth divisor in affine dimension at most one
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The low-dimensional case of the purity isomorphism used in Zhang, §2, before (†).
On an empty divisor both Weil complexes vanish. At a point of a nonempty divisor,
the local dimension formula forces the ambient affine space to have dimension one.
The divisor then has relative dimension zero. The closed-pair orientation gives the
inverse Tate twist and shift for constant coefficients (SGA 4, XVI, 3.8 and 3.10(a)).
Transport this orientation to the lisse sheaf `G`. -/
public theorem smoothDivisorRelativePurityLowDimension
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {I : Type u} [Finite I] (_hdim : Nat.card I < 2)
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (i : Y ⟶ 𝔸(I; Spec (CommRingCat.of k))) [IsSmoothAffineHypersurface i]
    [i.IsOver (Spec (CommRingCat.of k))]
    (G : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))) (hG : G.IsLisse) :
    letI := isNoetherian_of_locallyOfFiniteType
      (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    Nonempty ((WeilComplex.closedUpperShriek i i.openComplement.ι
      (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)).obj
        (WeilSheaf.toComplex.obj G) ≅
      (WeilSheaf.toComplex.obj (((WeilSheaf.upperStar i).obj G).tensorObj
        (WeilSheaf.tateTwistSheaf k ℓ Y (-1)) (hG.upperStar i)))⟦(-2 : ℤ)⟧) := by
  let a := 𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)
  have := isNoetherian_of_locallyOfFiniteType a
  by_cases hempty : IsEmpty Y
  · exact ⟨(WeilComplex.isZero_of_isEmpty _).iso (WeilComplex.isZero_of_isEmpty _)⟩
  have hdim : Nat.card I = 1 := by
    obtain ⟨y⟩ := not_isEmpty_iff.mp hempty
    obtain ⟨W, _, hy, n, m, hmn, hn, _⟩ :=
      IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension 1 i a
        (Smooth.isRegularLocalRing_stalk (i ≫ a)) y
    have : Nonempty W.toScheme := ⟨⟨i y, hy⟩⟩
    have hW : SmoothOfRelativeDimension (Nat.card I) (W.ι ≫ a) := by
      simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (Nat.card I) W.ι a
    have := SmoothOfRelativeDimension.eq_of_field _ hn hW
    omega
  have : SmoothOfRelativeDimension 1 a :=
    hdim ▸ AffineSpace.smoothOfRelativeDimension_over I (Spec (.of k))
  have : SmoothOfRelativeDimension 0 (Y ↘ Spec (.of k)) := by
    rw [← comp_over i (Spec (.of k))]
    exact smoothOfRelativeDimension_of_regularImmersion 1 1 i a
  obtain ⟨e, _⟩ := lisseClosedPurityOfConstant i (WeilSheaf.tateTwistSheaf k ℓ Y (-1)) (-2)
    (smoothClosedConstantOrientation 0 i)
  exact ⟨e G hG⟩

end WeilII
