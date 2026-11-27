module

import Mathlib.CategoryTheory.Abelian.Monomorphisms
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits
public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import WeilII.Paper.ChainSectionPolynomial
import WeilII.Paper.WeakLefschetz
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Ring.Finite
import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import WeilConjectures.WeilSheaf.BaseChangeField.CompactSupport
import WeilConjectures.WeilSheaf.TraceFunction
import WeilII.AlgebraicGeometry.AffineSpaceCohomologyWeightDescent
import WeilII.Paper.AffineSpaceCoordinateWeights
import WeilII.Paper.AffineLineArithmeticBaseChange
import WeilII.Paper.ExternalTensorPowerIso
import WeilII.Paper.GeometricChainSectionConcentration
import WeilII.Paper.WeightBoundOfRationalChainSection
import WeilII.Targets.Construction25
import WeilConjectures.WeilSheaf.ShiftedSheaf

/-!
# Weights of external tensor powers on affine space

Dingxin Zhang, *On an elementary proof of Weil II*, Proposition 1.5 (statement on p. 1,
proof on p. 4).
-/

open AlgebraicGeometry

namespace WeilII

/-- Zhang, Proposition 1.5. If a lisse sheaf `E` on the affine line over a finite field `k`
has pointwise weight at most `w`, then for each `n ≥ 2` its external tensor power has geometric
compactly supported cohomology in degree `n` of weight at most `n * (w + 1) + 3`.

Proof (Zhang, pp. 2–4). Fix n and put s = n(w + 1) + 3. Construction 2.5 gives a finite
extension K/k and a smooth hypersurface with equation P(x) = B(x) + ∑ aᵢxᵢ + c, where
B(x) = ∑ xᵢxᵢ₊₁. The hypersurface and the external tensor power G of the restricted sheaf
satisfy Definition 2.3. Write j for the open complement. The restricted sheaf retains its
pointwise weight bound, since extension of a residue field raises the local Frobenius and the
residue-field cardinality to the same power. Let r bound the stalk ranks.

For each m ≥ 1 take the degree-m extension L/K, with N = #L. Choose a nontrivial additive
character of K and compose it with the surjective field trace from L to obtain ψₘ. In the
alternating trace of Lemma 2.2 all degrees except n vanish. Thus the trace of the m-th
geometric Frobenius power on H_cⁿ(Rj_*j^*G), mapped to ℂ, is (−1)^(n+1) times the sum over
nonzero h in L of the exponential sums with phase ψₘ(hP(x)).

Write t for the stalk trace function over L, mapped to ℂ. For each h, absorb the linear terms
into the functions u ↦ t(u)ψₘ(haᵢu). Their supremum norms are at most r N^(w/2) by the
pointwise eigenvalue bound and the triangle inequality. The factor ψₘ(hc) has norm one and
u ↦ ψₘ(hu) is nontrivial. Lemma 2.6 bounds the inner sum by N^((n+1)/2) (r N^(w/2))^n.
Summing over N−1 values of h bounds the trace by r^n N^(s/2). With the same hypersurface and
positive constant max(1, r^n) for all m, Lemma 2.1 gives weight at most s over K.

If d = [K:k] and q = #k, base change identifies the external tensor power and its geometric
compactly supported cohomology, with Frobenius over K acting as the d-th power of Frobenius
over k. Each eigenvalue α over k therefore satisfies |ι(α)|^d ≤ (q^d)^(s/2). Taking d-th
roots gives the asserted bound over k. -/
public theorem affineLineExternalTensorPower_hnc_hasWeightsAtMost (k : Type*) [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (ι : PadicAlgCl ℓ →+* ℂ)
    (E : ProEtale.AdicSheaf ℓ (affineLine k)) (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (hw : WeilSheaf.HasWeightsAtMost ι (WeilSheaf.geometricFiberPullback (k₀ := k) hE) w)
    (n : ℕ) (hn : 2 ≤ n) :
    FrobeniusModule.HasWeightsAtMostOver k ι
      (WeilSheaf.compactlySupportedCohomology
        (affineLineExternalTensorPower (WeilSheaf.geometricFiberPullback (k₀ := k) hE)
          (WeilSheaf.isLisse_geometricFiberPullback hE) n) (n : ℤ))
      ((n : ℝ) * (w + 1) + 3) := open CategoryTheory in by
  let F := WeilSheaf.geometricFiberPullback (k₀ := k) hE
  let hF : F.IsLisse := WeilSheaf.isLisse_geometricFiberPullback hE
  let G := affineLineExternalTensorPower F hF n
  obtain ⟨K, hfin, a, c, hi, hgeom⟩ :=
    exists_smooth_chainSection_hasWeakLefschetz k ℓ E hE n hn
  let : FiniteDimensional k K := hfin
  let : Finite K := Module.finite_of_finite k
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  let f : affineLine K ⟶ affineLine k := AffineSpace.map PUnit (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let EK := (ProEtale.adicUpperStar ℓ f).obj E
  let hEK : ProEtale.IsAdicLisseSheaf EK := ProEtale.IsAdicLisseSheaf.upperStar f hE
  let FK := WeilSheaf.geometricFiberPullback (k₀ := K) hEK
  let hFK : FK.IsLisse := WeilSheaf.isLisse_geometricFiberPullback hEK
  let GK := affineLineExternalTensorPower FK hFK n
  obtain ⟨eF⟩ := affineLineArithmeticBaseChange_iso K E hE
  have hwK : FK.HasWeightsAtMost ι w := by
    apply WeilSheaf.HasWeightsAtMost.of_iso (X := affineLine K) (F := affineSpaceWeilSheafBaseChangeField K F) (G := FK) eF
    exact affineSpace_baseChangeField_hasWeightsAtMost K F ι w hw
  obtain ⟨base⟩ := affineLineExternalTensorPower_baseChangeField K F hF n hn
  obtain ⟨coeff⟩ := affineLineExternalTensorPower_isoOfIso eF
    (isLisse_affineSpaceWeilSheafBaseChangeField K hF) hFK n
  let eG : affineSpaceWeilSheafBaseChangeField K G ≅ GK := base ≪≫ coeff
  apply affineSpace_weightBound_of_baseChangeField K G ι n _ GK eG
  apply externalTensorPower_weightBound_of_rationalChainSection K ℓ ι EK hEK w hwK n hn
  refine ⟨a, c, hi, ?_⟩
  exact chainSection_subsingleton_of_geometric_weakLefschetz F hF n hn K
    (chainSectionPolynomial a c) GK eG hgeom

end WeilII
