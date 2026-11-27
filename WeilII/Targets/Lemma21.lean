module

import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits
public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import WeilII.Paper.GeometricExternalTensorPowerLisse
import WeilII.Paper.ExternalTensorPowerLisse
import WeilII.AlgebraicGeometry.SmoothHypersurfaceGysinInjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceBound

/-!
# The trace criterion for external tensor powers

Dingxin Zhang, *On an elementary proof of Weil II*, Lemma 2.1, p. 2.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Zhang, Lemma 2.1, p. 2. Fix an external tensor power of degree `n ≥ 2`. If one smooth
hypersurface and one positive constant give the indicated trace bound for all positive
Frobenius powers, then the weight bound of Proposition 1.5 holds in degree `n`.

Proof. Write `q = #k`, `s = n(w+1)+3`, and `R = q^(s/2) > 0`. For the given hypersurface
and its open complement `j`, let `W = H_cⁿ(Rj_* j^* G)`. The hypothesis bounds the absolute
value of the embedded trace of the m-th Frobenius power on W by `C R^m`. This trace is the
sum of the m-th powers of the embedded eigenvalues, counted with multiplicity. The power
series with these traces as coefficients of `T^(m-1)` converges for `|T| < 1/R`. Near zero
it equals the sum of `λ/(1-λT)` over those eigenvalues. Each distinct nonzero λ contributes
a pole at its reciprocal, since its multiplicity is positive and the other distinct terms
are regular there. Thus every eigenvalue has absolute value at most R.

The external tensor power G is lisse. Relative purity for the smooth hypersurface and the
localization triangle give the Frobenius-equivariant exact sequence (†). The term preceding
`H_cⁿ(G) → W` is `H_c^(n-2)(Y, i^*G(-1))`. On the smooth affine geometric hypersurface of
dimension `n-1`, Poincaré duality pairs this group with ordinary cohomology in degree `n`
of the twisted dual local system. Artin vanishing kills that group. Hence the map to W is
injective, and maps every nonzero Frobenius eigenvector to one with the same eigenvalue.
The bound for W therefore holds on `H_cⁿ(G)`. -/
public theorem affineLineExternalTensorPower_hnc_hasWeightsAtMost_of_trace_bound
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ι : PadicAlgCl ℓ →+* ℂ) (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (hw : WeilSheaf.HasWeightsAtMost ι (WeilSheaf.geometricFiberPullback (k₀ := k) hE) w)
    (n : ℕ) (hn : 2 ≤ n) :
    let G := affineLineExternalTensorPower (WeilSheaf.geometricFiberPullback (k₀ := k) hE)
      (WeilSheaf.isLisse_geometricFiberPullback hE) n
    let s := (n : ℝ) * (w + 1) + 3
    (∃ (Y : Scheme.{u}) (i : Y ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)))
        (_ : IsSmoothAffineHypersurface i) (C : ℝ), 0 < C ∧
      letI := isNoetherian_of_locallyOfFiniteType
        (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      let W := WeilComplex.compactlySupportedCohomology
        (openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G) (n : ℤ)
      ∀ m : ℕ, 1 ≤ m → ‖ι (LinearMap.trace (PadicAlgCl ℓ) _ (W.frobeniusEnd ^ m))‖ ≤
        C * ((Nat.card k : ℝ) ^ m) ^ (s / 2)) →
    FrobeniusModule.HasWeightsAtMostOver k ι (G.compactlySupportedCohomology (n : ℤ)) s := by
  intro G s
  rintro ⟨Y, i, hi, C, _, htrace⟩
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let W := WeilComplex.compactlySupportedCohomology
    (openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G) (n : ℤ)
  have hW : W.HasWeightsAtMost ι (Nat.card k) s := by
    apply FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le
      (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') W (C := C)
    intro m hm
    rw [Real.rpow_pow_comm (Nat.cast_nonneg (Nat.card k))]
    exact htrace m hm
  have hG : G.IsLisse := affineLineExternalTensorPower_isLisse _ _ n hn
  obtain ⟨f, hinj, hf⟩ := exists_injective_smoothHypersurfaceRestriction hn i G hG
  exact FrobeniusModule.HasWeightsAtMost.of_injective (M := G.compactlySupportedCohomology n)
    (N := W) f hf hinj hW

end WeilII
