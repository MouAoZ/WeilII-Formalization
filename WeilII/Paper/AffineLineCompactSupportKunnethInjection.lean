module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilII.LinearAlgebra.FrobeniusModulePositiveTensorPower
public import WeilII.Paper.AffineLineExternalTensorPower
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.WeilSheaf.TateTwistCohomology
import WeilII.AlgebraicGeometry.AffineSpaceLastCoordinatePullback
import WeilII.AlgebraicGeometry.CompactSupportKunnethSummand
import WeilII.Paper.ExternalTensorPowerLastFactor
import WeilII.Paper.ExternalTensorPowerLisse

/-!
# The degree-one tensor summand in compactly supported cohomology of affine space

Dingxin Zhang, *On an elementary proof of Weil II*, p. 2, first display in the deduction
of Theorem 1.1 from Proposition 1.5.
-/

open AlgebraicGeometry

namespace WeilII

/-- The Frobenius-equivariant Künneth injection in Zhang, p. 2. For a lisse Weil sheaf on
the affine line, the ordered tensor power of its degree-one compactly supported cohomology
embeds into degree `n` of the external tensor power.

Proof. Write V for the degree-one group. Start in arity one with the identity of V, using
the affine line of E itself. At each step split the coordinates into the first r and the
last. These projections exhibit affine (r+1)-space as the product over k: on every test
k-scheme, a tuple of r+1 global functions is uniquely specified by its first r entries
and its last entry. In the first step both projections have target the affine line of E.

The first r factors give a lisse coefficient, since pullback and tensor preserve lissity.
Apply binary compact-support Künneth to this coefficient and E in total degree r+1. Include
the (r,1) summand in the direct sum. Projection to that summand is a left inverse, and the
Künneth isomorphism sends pure tensors to exterior products. Geometric Frobenius preserves
these products by pullback along the two projections and acts on each factor through its
Weil structure. The last-factor isomorphism identifies the product coefficient with the
specified external power, inducing a Frobenius-equivariant cohomology isomorphism.

Compose the resulting inclusion with the preceding injection tensored on the right with
the identity of V. Tensoring preserves injectivity over the coefficient field. Equivariance
holds on pure tensors by the preceding step and hence on their span. Induction gives the
inclusion of the (1,…,1) summand in arity n. -/
public theorem affineLineCompactSupportKunnethInjection
    {k : Type*} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse) (n : ℕ) (hn : 2 ≤ n) :
    let V := WeilSheaf.compactlySupportedCohomology E 1
    let T := V.positiveTensorPower n (lt_of_lt_of_le Nat.zero_lt_two hn)
    let W := WeilSheaf.compactlySupportedCohomology (affineLineExternalTensorPower E hE n) (n : ℤ)
    ∃ u : T.carrier →ₗ[PadicAlgCl ℓ] W.carrier,
      Function.Injective u ∧ ∀ x, u (T.frobenius x) = W.frobenius (u x) := open CategoryTheory in by
  let V := E.compactlySupportedCohomology 1
  let H (r : ℕ) := (affineLineExternalTensorPower E hE r).compactlySupportedCohomology (r : ℤ)
  change (V.positiveTensorPower n _).Embeds (H n)
  induction n, hn using Nat.le_induction with
  | base =>
    rw [FrobeniusModule.positiveTensorPower.eq_3, FrobeniusModule.positiveTensorPower.eq_2]
    let proj (i : Fin 2) := AffineSpace.reindex (fun _ : PUnit ↦ ULift.up i) (Spec (.of k))
    -- Keep the projection witnesses abstract while identifying the two coordinate factors.
    have includePair {hp : (proj 0).IsOver (Spec (.of k))}
        {hs : (proj (Fin.last 1)).IsOver (Spec (.of k))}
        {A B : {D : WeilSheaf k ℓ 𝔸(ULift (Fin 2); Spec (.of k)) // D.IsLisse}}
        (left : A = @affineLineExternalTensorPower.pullLisse k _ _ ℓ _ _ _ _ _ _ (proj 0) hp E hE)
        (right : B = @affineLineExternalTensorPower.pullLisse k _ _ ℓ _ _ _ _ _ _
          (proj (Fin.last 1)) hs E hE)
        (coeff : Nonempty (A.1.tensorObj B.1 A.2 ≅ affineLineExternalTensorPower E hE 2)) :
        (V.tensor V).Embeds (H 2) := by
      subst A B
      exact compactSupportKunnethSummand (proj 0) (proj (Fin.last 1))
        (affineSpaceLastCoordinatePullback (Spec (.of k)) (Equiv.ofUnique _ (Fin 1)))
        E E hE hE _ ⟨_, coeff⟩ 1 1
    exact includePair (affineLineExternalTensorPower.coordinateFactor.eq_1 E hE 0)
      (affineLineExternalTensorPower.coordinateFactor.eq_1 E hE (Fin.last 1))
      (affineLineExternalTensorPower_lastFactor E hE).1
  | succ r hr ih =>
    have pow : V.positiveTensorPower (r + 1) (by omega) =
        (V.positiveTensorPower r (by omega)).tensor V := by
      cases r with
      | zero => omega
      | succ m => exact FrobeniusModule.positiveTensorPower.eq_3 _ _ _
    rw [pow]
    apply ih.rTensor_trans
    -- Use the structure map of E's affine line for its coefficient and the structure map
    -- of the one-coordinate affine space for the reindexing, as in the last-factor formula.
    exact compactSupportKunnethSummand (Y := 𝔸(PUnit; Spec (.of k)))
      (overY := @CanonicallyOverClass.toOverClass _ _ (affineLine k) _ (AffineSpace.over _ _))
      (AffineSpace.reindex (fun i : ULift (Fin r) ↦ ULift.up i.down.castSucc) (Spec (.of k)))
      (AffineSpace.reindex (fun _ : PUnit ↦ ULift.up (Fin.last r)) (Spec (.of k)))
      (over_p := ⟨AffineSpace.reindex_over _ _⟩)
      (over_s := @HomIsOver.mk _ _ _ _ _ _ _
        (@CanonicallyOverClass.toOverClass _ _ 𝔸(PUnit; Spec (.of k)) _ (AffineSpace.over _ _))
        (AffineSpace.reindex_over _ _))
      (affineSpaceLastCoordinatePullback (Spec (.of k)) Equiv.ulift)
      (affineLineExternalTensorPower E hE r) E (affineLineExternalTensorPower_isLisse E hE r hr) hE
      (affineLineExternalTensorPower E hE (r + 1))
      ((affineLineExternalTensorPower_lastFactor E hE).2 r hr) (r : ℤ) 1

end WeilII
