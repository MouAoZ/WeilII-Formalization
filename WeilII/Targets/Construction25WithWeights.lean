module

import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import WeilII.Targets.Construction25
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Construction 2.5 for the sheaf of Proposition 1.5

Dingxin Zhang, *On an elementary proof of Weil II*, pp. 1–3.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Zhang, Construction 2.5, p. 3. For the lisse sheaf of pointwise weight at most `w`
of Proposition 1.5, a finite extension admits a smooth chain section satisfying weak
Lefschetz for the geometric external tensor power.

Proof. Apply the chain-section existence theorem for arbitrary lisse sheaves to `E`.
It gives one finite extension and one tuple of coefficients witnessing both properties. -/
public theorem exists_smooth_chainSection_hasWeakLefschetz_of_hasWeightsAtMost
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ι : PadicAlgCl ℓ →+* ℂ) (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (_hw : WeilSheaf.HasWeightsAtMost ι (WeilSheaf.geometricFiberPullback (k₀ := k) hE) w)
    (n : ℕ) (hn : 2 ≤ n) :
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
  exact exists_smooth_chainSection_hasWeakLefschetz k ℓ E hE n hn

end WeilII
