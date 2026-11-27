module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilII.Paper.AffineHyperplaneFamily
public import WeilII.Paper.WeakLefschetz
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.OpenComplementVerdierDuality
import WeilII.Paper.AffineProjectiveHyperplaneFiber
import WeilII.Paper.KatzGenericHyperplaneLisseExtensionByZero
import WeilII.Paper.WeakLefschetzDualCriterion

/-!
# Generic affine hyperplane weak Lefschetz

Dingxin Zhang, *On an elementary proof of Weil II*, Theorem 2.4, p. 3, applying
Katz, *Affine cohomological transforms, perversity, and monodromy*, Corollary A.5.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory

universe u

/-- Zhang, Theorem 2.4, p. 3. For a quasi-finite morphism of geometric affine spaces and
a lisse sheaf on its source, one nonempty dense open of affine hyperplanes works for every
geometric parameter in it. The ambient dimension is positive, as in Katz, Appendix A, p. 218.

Proof. Write `X = 𝔸ⁿ` and compose `u` with the standard affine chart into projective
`N`-space. The composite is quasi-finite, separated and of finite type. The sheaf
`L = Gᵛ(n)` is lisse, so its shift `L[n]` is perverse on the smooth pure-dimensional `X`.
Katz A.5 gives a dense open of projective hyperplanes on which
`Hʳ(X, j_! j^*L) = 0` for `r < n`. Intersect with the affine hyperplane parameter
open. This open is nonempty since `N > 0`, and the dual projective space is irreducible,
so the intersection is nonempty and dense in the parameter space. On the standard
affine chart the projective equation pulls back to `c + ∑ aᵢuᵢ`, hence `j` is precisely
the complement of the scheme-theoretic inverse image of the affine hyperplane.
When `n > 0`, quasi-finiteness forces some `uᵢ` to be nonconstant. Keeping one of its
positive-degree monomial coefficients nonzero in the linear combination shrinks the open
to hyperplanes whose inverse images are hypersurfaces. When `n = 0`, one may instead
take the open of hyperplanes avoiding the image point.

Verdier duality identifies the dual of `H_c^e(X, Rj_* j^*G)` with
`H^{2n-e}(X, j_! j^*L)`. For `e > n` the latter vanishes by the choice of the open.
For `e < n` it vanishes by Artin's affine cohomological dimension bound, since
`j_! j^*L` is a constructible sheaf in degree zero. Duals over a field detect zero.
This proves Definition 2.3 for every hyperplane in that same open. -/
public theorem exists_denseOpen_affineHyperplane_hasWeakLefschetz
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (n N : ℕ) (_hN : 0 < N) :
    let K := AlgebraicClosure k
    let S := Spec (CommRingCat.of K)
    let I := ULift.{u} (Fin n)
    let J := ULift.{u} (Fin N)
    let T := (affineHyperplaneParameter J S).toScheme
    letI : S.Over S := ⟨𝟙 S⟩
    letI : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
    ∀ (u : 𝔸(I; S) ⟶ 𝔸(J; S)) [u.IsOver S] [LocallyQuasiFinite u]
      (G : ProEtale.AdicSheaf ℓ 𝔸(I; S)) (hG : ProEtale.IsAdicLisseSheaf G),
      ∃ U : T.Opens, (U : Set T).Nonempty ∧ Dense (U : Set T) ∧
        ∀ (A : S ⟶ T) [A.IsOver S], A (IsLocalRing.closedPoint K) ∈ U →
          HasWeakLefschetz (affineHyperplaneInverseImage u A).subschemeι G hG := by
  classical
  intro K S I J T v hv hqf G hG
  let B := affineHyperplaneParameter J S
  let b : J := ⟨⟨0, _hN⟩⟩
  have : Nontrivial (Option J) := ⟨⟨none, some b, by simp⟩⟩
  let P := ℙ(Option J; S)
  let X := 𝔸(I; S)
  have : SmoothOfRelativeDimension n (X ↘ S) := by
    have hn : Nat.card I = n := by simp [I]
    simpa only [hn] using AffineSpace.smoothOfRelativeDimension_over I S
  obtain ⟨c, hc, hcOpen, hfiber⟩ := exists_affineChart_comap_projectiveHyperplaneFiber K J
  obtain ⟨L, hL, test⟩ := exists_lisse_hasWeakLefschetz_of_lower_vanishing k ℓ n G hG
  obtain ⟨W, hW, vanish⟩ := exists_denseOpen_isZero_lisse_hyperplaneExtensionByZero k ℓ
    (Option J) n (v ≫ c) L hL
  let U := B.ι ⁻¹ᵁ W
  have hU : Dense (U : Set T) := hW.preimage B.ι.isOpenEmbedding.isOpenMap
  let D := ProjectiveSpace.standardOpen (Option J) S (some b)
  have hDB : D ≤ B := le_iSup (fun i : J ↦ ProjectiveSpace.standardOpen (Option J) S (some i)) b
  let chartPoint := AffineSpace.zeroSection {i : Option J // i ≠ some b} S ≫
    (ProjectiveSpace.standardOpenIso (Option J) S (some b)).inv ≫ P.homOfLE hDB
  have : Nonempty T := ⟨chartPoint (IsLocalRing.closedPoint K)⟩
  refine ⟨U, hU.nonempty, hU, ?_⟩
  intro A hA hAU
  apply test
  rw [hfiber v A]
  exact vanish (A ≫ B.ι) hAU

end WeilII
