module

public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology

/-!
# Weak Lefschetz for a hypersurface and a lisse sheaf

Zhang, *On an Elementary Proof of Weil II*, Definition 2.3, p. 3, uses the open complement
of a hypersurface in geometric affine space. For a pair over a finite field, one takes the
closed immersion and the sheaf on the geometric fiber.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The weak Lefschetz property of Zhang, Definition 2.3, p. 3. For the inclusion `i` of the
hypersurface and its open complement `j`, the groups `H_c^e(𝔸ⁿ, Rj_* j^* G)` vanish in every
integer degree except possibly `n`, the number of affine coordinates. The formula takes the
closed immersion directly, so it is independent of a defining equation for the hypersurface. -/
@[expose] public def HasWeakLefschetz {K : Type u} [Field K] [IsAlgClosed K]
    {I : Type u} [Finite I] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar K ≠ ℓ)] {Y : Scheme.{u}}
    (i : Y ⟶ 𝔸(I; Spec (CommRingCat.of K))) [IsClosedImmersion i]
    (G : ProEtale.AdicSheaf ℓ 𝔸(I; Spec (CommRingCat.of K)))
    (_hG : ProEtale.IsAdicLisseSheaf G) : Prop :=
  let j := i.openComplement.ι
  let restriction := (ProEtale.adicUpperStar ℓ j).obj G
  let directImage := (ProEtale.adicLowerStar ℓ j).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj restriction)
  let a := 𝔸(I; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)
  ∀ e : ℤ, e ≠ (Nat.card I : ℤ) →
    IsZero ((ProEtale.algClosedCompactlySupportedCohomology ℓ a e).obj directImage)

end WeilII
