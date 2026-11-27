module

import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits
public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import WeilII.AlgebraicGeometry.SmoothHypersurfaceGysinSequence
import WeilII.Paper.GeometricExternalTensorPowerLisse
import WeilConjectures.LinearAlgebra.TraceLongExactSequenceFinsum
import WeilConjectures.WeilSheaf.Finiteness
import WeilConjectures.WeilSheaf.StalkTateTwist
import WeilConjectures.WeilSheaf.StalkTensorTrace
import WeilConjectures.WeilSheaf.TraceFunction
import WeilConjectures.WeilSheaf.TraceFunctionCongr
import WeilConjectures.WeilSheaf.TraceFunctionOps
import WeilConjectures.ZetaFunction.TraceFormula
import WeilConjectures.ZetaSeries
import WeilII.Paper.ExternalTensorPowerHypersurfaceTrace
import WeilII.Paper.NonzeroFrequencySum

/-!
# The exponential-sum formula for the open restriction

Dingxin Zhang, *On an elementary proof of Weil II*, Lemma 2.2 and (2.2.1), p. 3.
-/

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace WeilII

universe u

/-- Zhang, Lemma 2.2, p. 3. For the smooth hypersurface cut out by `P`, the alternating
trace of the m-th geometric Frobenius power on `H_c^*(Rj_* j^*(E^{⊠n}))` equals the
negative sum over nonzero frequencies and all coordinate tuples in the degree-m extension.

Proof. Put `G = E^{⊠n}`, `Y = V(P)`, and let j include the open complement. The geometric
sheaf G is lisse. The Frobenius-equivariant Gysin sequence on p. 2 and additivity of traces
in finite exact sequences express the alternating trace of the open term as the alternating
trace for G on affine space minus that for `i^*G(-1)` on Y. Indeed, only finitely many degrees
contribute, and the degree shift by two on the closed term preserves the alternating sign.

Apply the Grothendieck trace formula to both terms over the same extension L/k of degree m.
At a tuple x, pullback along each projection gives the stalk at its coordinate, and the trace
of the tensor product is the product `T(x) = ∏ᵢ t(xᵢ)` of the embedded traces. The L-points
of Y are the tuples with P(x)=0. The negative Tate twist multiplies their stalk traces by
the cardinality of L. Thus (2.2.1) is the sum of T over all tuples minus the cardinality
of L times its sum over the zeros of P.

The field trace onto k is surjective, so ψ composed with it is nontrivial. Summing this
character at hP(x) over all h in L gives the cardinality of L when P(x)=0. For P(x) nonzero,
translation by a suitable h multiplies the sum by a character value different from one,
so the sum vanishes. Substitute this identity into (2.2.1) and exchange the finite sums.
The zero frequency contributes the full affine sum and cancels it, leaving the stated sign. -/
public theorem affineLineExternalTensorPower_alternatingTrace_eq_neg_sum
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ι : PadicAlgCl ℓ →+* ℂ) (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (hw : WeilSheaf.HasWeightsAtMost ι (WeilSheaf.geometricFiberPullback (k₀ := k) hE) w)
    (n : ℕ) (hn : 2 ≤ n) (P : MvPolynomial (Fin n) k) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
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
        -(∑ h : Lˣ, ∑ x : Fin n → L, (∏ r, t (x r)) *
          ψ.compTrace L ((h : L) * MvPolynomial.eval₂ (algebraMap k L) x P)) := by
  intro S X coeff p i hi m hm F G D L t
  let : Finite L := Module.finite_of_finite k
  let := Fintype.ofFinite L
  exact (affineLineExternalTensorPower_alternatingTrace_eq_affine_sub_zero_sum
    k ℓ ι E hE n hn P hi m hm).trans
      (sub_card_mul_sum_zeros_eq_neg_sum_units ψ hψ
        (fun x : Fin n → L ↦ ∏ r, t (x r)) (fun x ↦ MvPolynomial.eval₂ (algebraMap k L) x P))

end WeilII
