module

public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import WeilII.AlgebraicGeometry.AffineHypersurfaceFieldPointCoordinates
import WeilII.Paper.ExternalTensorPowerOpenTrace
import WeilII.Paper.ExternalTensorPowerPointTrace

/-!
# The exponential-sum formula for the open restriction

Dingxin Zhang, *On an elementary proof of Weil II*, Lemma 2.2 and (2.2.1), p. 3.
-/

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace WeilII

universe u

/-- Zhang, equation (2.2.1), p. 3. Express the two field-point sums for the open
trace in affine coordinates. Pullbacks along the projections select the corresponding
coordinates, so the embedded external-power trace is the product of the embedded
coordinate traces. The hypersurface equivalence reads those same coordinates after
the closed immersion, with image exactly the zero tuples. Reindex both sums. -/
public theorem affineLineExternalTensorPower_alternatingTrace_eq_affine_sub_zero_sum
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ι : PadicAlgCl ℓ →+* ℂ) (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E)
    (n : ℕ) (hn : 2 ≤ n) (P : MvPolynomial (Fin n) k) :
    let S := Spec (CommRingCat.of k)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ S).appTop).hom
    let p := MvPolynomial.eval₂Hom coeff (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i)) P
    let i := X.zeroLocusSubschemeι {p}
    IsSmoothAffineHypersurface i → ∀ m : ℕ, 1 ≤ m →
      letI := isNoetherian_of_locallyOfFiniteType (X ↘ S)
      let F := WeilSheaf.geometricFiberPullback (k₀ := k) hE
      let G := affineLineExternalTensorPower F (WeilSheaf.isLisse_geometricFiberPullback hE) n
      let D := openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G
      let L := FiniteField.galoisExtension k m
      letI : Finite L := Module.finite_of_finite k
      letI := Fintype.ofFinite L
      let t := fun a : L ↦ ι (F.traceFunction m ((AffineSpace.fieldPointsEquiv k L).symm a))
      (∑ᶠ e : ℤ, (e.negOnePow : ℤ) • ι (LinearMap.trace (PadicAlgCl ℓ) _
        ((D.compactlySupportedCohomology e).frobeniusEnd ^ m))) =
        (∑ x : Fin n → L, ∏ r, t (x r)) - (Fintype.card L : ℂ) *
          ∑ x : {x : Fin n → L // MvPolynomial.eval₂ (algebraMap k L) x P = 0}, ∏ r, t (x.1 r) := by
  intro S X coeff p i hi m hm F G D L t
  let a := X ↘ S
  let : (X.zeroLocusSubscheme {p}).Over S := ⟨i ≫ a⟩
  let : i.IsOver S := ⟨rfl⟩
  let : Finite L := Module.finite_of_finite k
  let := Fintype.ofFinite L
  let hF := WeilSheaf.isLisse_geometricFiberPullback (k₀ := k) hE
  let coords := (AffineSpace.fieldPointsEquivPi (ULift.{u} (Fin n)) k L).trans
    (Equiv.ulift.arrowCongr (Equiv.refl L))
  let Pval := fun x : Fin n → L ↦ MvPolynomial.eval₂ (algebraMap k L) x P
  let zeros := affineHypersurfaceFieldPoints k L P
  let T := fun x : Fin n → L ↦ ∏ r, t (x r)
  have pointTrace (x : a.fieldPoints L) : ι (G.traceFunction m x) = T (coords x) := by
    exact (congrArg ι (traceFunction_externalTensorPower F hF (by omega : 0 < n) m x)).trans
      (map_prod ι _ _)
  have sumX : (∑ᶠ x : a.fieldPoints L, ι (G.traceFunction m x)) = ∑ x, T x :=
    (finsum_congr pointTrace).trans
      ((finsum_comp_equiv coords (f := T)).trans (finsum_eq_sum_of_fintype _))
  have pointY (y : (i ≫ a).fieldPoints L) :
      ι (G.traceFunction m (i.mapFieldPoints L y)) = T (zeros y).1 :=
    (pointTrace _).trans (congrArg T (affineHypersurfaceFieldPoints_apply k L P y).symm)
  have sumY : (∑ᶠ y : (i ≫ a).fieldPoints L, ι (G.traceFunction m (i.mapFieldPoints L y))) =
      ∑ z : {x // Pval x = 0}, T z :=
    (finsum_congr pointY).trans
      ((finsum_comp_equiv zeros (f := fun z ↦ T z.1)).trans (finsum_eq_sum_of_fintype _))
  exact (affineLineExternalTensorPower_openTrace_eq_fieldPointSums k ℓ ι E hE n hn P hi m hm).trans
    (congrArg₂ (· - ·) sumX (congrArg ((Fintype.card L : ℂ) * ·) sumY))

end WeilII
