module

public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.TraceFunctionOps
import WeilConjectures.ZetaSeries
import WeilII.AlgebraicGeometry.SmoothHypersurfaceOpenTrace
import WeilII.Paper.ExternalTensorPowerLisse

/-!
# The open trace as a difference of field-point sums

Dingxin Zhang, *On an elementary proof of Weil II*, Lemma 2.2 and (2.2.1), p. 3.
-/

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace WeilII

universe u

/-- The cohomological subtraction in Zhang, equation (2.2.1), p. 3, before expressing the
point sums in affine coordinates. For the external power G, the open trace is
the full sum of its point traces minus (#k)^m times their sum on the hypersurface.

Proof. Pullback along each coordinate preserves lissity and so does the tensor product.
Apply the Frobenius-equivariant Gysin sequence of the smooth closed immersion to G.
In degree r its terms are the compactly supported cohomology of i*G(−1) in degree r−2,
of G in degree r and of the open direct image in degree r. Each family vanishes outside
a finite interval. Translate the closed interval by two and take the union to bound all
three. Equivariance gives additivity of the alternating m-th power traces on this bounded
exact sequence. Move the shifted closed trace to the other side. The Grothendieck trace
formula identifies the unshifted affine term with the full point sum. For the closed term
the shift by two preserves the signs. The twist minus one contributes the scalar (#k)^m,
and the restricted trace at y evaluates G at i(y). The field embedding respects finite sums and products. Since the degree-m
extension has cardinality (#k)^m, this gives the displayed difference. -/
public theorem affineLineExternalTensorPower_openTrace_eq_fieldPointSums
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
      letI : (X.zeroLocusSubscheme {p}).Over S := ⟨i ≫ X ↘ S⟩
      letI : i.IsOver S := ⟨rfl⟩
      let F := WeilSheaf.geometricFiberPullback (k₀ := k) hE
      let G := affineLineExternalTensorPower F (WeilSheaf.isLisse_geometricFiberPullback hE) n
      let D := openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G
      let L := FiniteField.galoisExtension k m
      letI : Finite L := Module.finite_of_finite k
      letI := Fintype.ofFinite L
      (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • ι (LinearMap.trace (PadicAlgCl ℓ) _
        ((D.compactlySupportedCohomology r).frobeniusEnd ^ m))) =
        (∑ᶠ x : (X ↘ S).fieldPoints L, ι (G.traceFunction m x)) -
          (Fintype.card L : ℂ) *
            ∑ᶠ y : (i ≫ X ↘ S).fieldPoints L, ι (G.traceFunction m (i.mapFieldPoints L y)) := by
  intro S X coeff p i hi m hm F G D L
  let a := X ↘ S
  let : (X.zeroLocusSubscheme {p}).Over S := ⟨i ≫ a⟩
  let : i.IsOver S := ⟨rfl⟩
  let : Finite L := Module.finite_of_finite k
  let := Fintype.ofFinite L
  have hG : G.IsLisse :=
    affineLineExternalTensorPower_isLisse F (WeilSheaf.isLisse_geometricFiberPullback hE) n hn
  let tr (r : ℤ) :=
    LinearMap.trace (PadicAlgCl ℓ) _ ((D.compactlySupportedCohomology r).frobeniusEnd ^ m)
  let tx (x : a.fieldPoints L) := G.traceFunction m x
  let ty (y : (i ≫ a).fieldPoints L) := G.traceFunction m (i.mapFieldPoints L y)
  have diff : (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • tr r) =
      finsum tx - (Nat.card k : PadicAlgCl ℓ) ^ m * finsum ty := by
    -- Identify the open direct images before applying cohomology and taking traces.
    let traceSum (M : WeilComplex k ℓ X) :=
      ∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl ℓ) _
        ((M.compactlySupportedCohomology r).frobeniusEnd ^ m)
    exact (fun {M} (p : traceSum M = _) (h : D = M) ↦ (congrArg traceSum h).trans p)
      (smoothHypersurface_openTrace_eq_sub i G hG hm) rfl
  have cardL : Fintype.card L = Nat.card k ^ m :=
    (Nat.card_eq_fintype_card (α := L)).symm.trans
      (FiniteField.nat_card_galoisExtension k m (Nat.ne_of_gt hm))
  have scalar : ι ((Nat.card k : PadicAlgCl ℓ) ^ m) = (Fintype.card L : ℂ) := by
    rw [map_pow, map_natCast, cardL, Nat.cast_pow]
  change (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • ι (tr r)) =
    (∑ᶠ x, ι (tx x)) - (Fintype.card L : ℂ) * ∑ᶠ y, ι (ty y)
  have leftMap := ι.toAddMonoidHom.map_finsum_of_injective ι.injective
    (fun r : ℤ ↦ (r.negOnePow : ℤ) • tr r)
  have signedMap := finsum_congr (fun r : ℤ ↦ (map_zsmul ι (r.negOnePow : ℤ) (tr r)).symm)
  refine signedMap.trans (leftMap.symm.trans ((congrArg ι diff).trans ?_))
  rw [map_sub, map_mul, scalar]
  have xmap : ι (finsum tx) = ∑ᶠ x, ι (tx x) :=
    ι.toAddMonoidHom.map_finsum_of_injective ι.injective tx
  have ymap : ι (finsum ty) = ∑ᶠ y, ι (ty y) :=
    ι.toAddMonoidHom.map_finsum_of_injective ι.injective ty
  exact congrArg₂ (· - ·) xmap (congrArg ((Fintype.card L : ℂ) * ·) ymap)

end WeilII
