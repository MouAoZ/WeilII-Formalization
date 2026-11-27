module

public import WeilII.Paper.ChainSectionPolynomial
public import WeilII.Paper.GeometricExternalTensorPowerLisse
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilII.Paper.WeakLefschetz
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilII.AlgebraicGeometry.AffinePolynomialSectionBaseChange
import WeilII.Paper.ChainGraphBasicOpenWeakLefschetz
import WeilII.Paper.SmoothChainSectionFinitePointInBasicOpen

/-!
# A smooth chain section satisfying weak Lefschetz

Dingxin Zhang, *On an elementary proof of Weil II*, Construction 2.5, p. 3,
with the finite-extension convention on p. 2.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Zhang, Construction 2.5. After a finite extension of the ground field there are
coefficients `a` and `c` whose chain equation defines a smooth hypersurface. Its geometric
fiber and the geometric external tensor power of `E` satisfy Definition 2.3.

Proof. Work over the algebraic closure. Write Q for the sum of products of consecutive
coordinates. The graph of Q is a closed immersion into affine (n+1)-space since its
coordinate ring map is surjective. It is therefore quasi-finite. Apply Theorem 2.4 to this
graph and the lisse geometric external tensor power to obtain a dense open of hyperplanes.
In the chart where the last coordinate has nonzero coefficient, normalize that coefficient
to one. Pulling back the hyperplane equation along the graph gives P = Q + ∑ aᵢXᵢ + c.

The smooth sections contain a nonempty open in this chart. Indeed, at a singular zero x
the gradient equations force a = −∇Q(x), and Euler's identity for Q then gives c = Q(x)
in every characteristic. The n+1 polynomials (−∇Q,Q) in n variables satisfy a nonzero
polynomial relation. Off its zero locus the Jacobian criterion gives smoothness. Intersect
this open with the dense open from Theorem 2.4. The intersection contains a nonempty
principal open and hence a point over the infinite algebraic closure.

Adjoin the finitely many coefficients of this point to k. They are algebraic, so the
resulting intermediate field L is finite over k. For n ≥ 2 the coefficient of X₁X₂ in P
is one. Thus P is a nonzero nonunit in the polynomial ring over L and cuts out a Cartier
divisor. Its coordinate ring becomes the smooth geometric quotient after tensoring with
the algebraic closure. Smoothness descends along this faithfully flat field extension.
Pulling the equation back to the closure recovers the chosen section, so Theorem 2.4 gives
weak Lefschetz for its open complement and the same geometric sheaf. -/
public theorem exists_smooth_chainSection_hasWeakLefschetz (k : Type u) [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E) (n : ℕ) (hn : 2 ≤ n) :
    let K := AlgebraicClosure k
    let I := ULift.{u} (Fin n)
    letI : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
    let hG := geometricExternalTensorPowerLisse (WeilSheaf.geometricFiberPullback (k₀ := k) hE)
      (WeilSheaf.isLisse_geometricFiberPullback hE) n hn K AlgEquiv.refl
    ∃ L : IntermediateField k K, FiniteDimensional k L ∧ ∃ (a : Fin n → L) (c : L),
      let S := Spec (CommRingCat.of L)
      let X := 𝔸(I; S)
      let coeff := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (X ↘ S).appTop).hom
      let p := MvPolynomial.eval₂Hom coeff (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i))
        (chainSectionPolynomial a c)
      let i := X.zeroLocusSubschemeι {p}
      let b := AffineSpace.map I (Spec.map (CommRingCat.ofHom (algebraMap L K)))
      let iBar := 𝔸(I; Spec (CommRingCat.of K)).zeroLocusSubschemeι {b.appTop p}
      IsSmoothAffineHypersurface i ∧ HasWeakLefschetz iBar _ hG := by
  intro K I hG
  obtain ⟨g, hg, hweak⟩ := exists_chainSection_basicOpen_hasWeakLefschetz k ℓ n hn _ hG
  obtain ⟨L, hL, a, c, hpoint, hsmooth⟩ :=
    exists_smooth_chainSection_finitePoint_in_basicOpen k n hn g hg
  refine ⟨L, hL, a, c, ?_⟩
  intro S X coeff p i b iBar
  refine ⟨hsmooth, ?_⟩
  let φ := CommRingCat.ofHom (algebraMap L K)
  have hmap : MvPolynomial.map φ.hom (chainSectionPolynomial a c) =
      chainSectionPolynomial (fun r ↦ φ.hom (a r)) (φ.hom c) := by
    cases n <;> simp [chainSectionPolynomial, map_sum]
  dsimp only [iBar, b, p]
  rw [affineSpace_map_appTop_eval₂Hom φ ULift.up (chainSectionPolynomial a c), hmap]
  exact hweak _ _ hpoint

end WeilII
