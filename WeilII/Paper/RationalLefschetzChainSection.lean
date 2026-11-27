module

public import WeilII.AlgebraicGeometry.OpenImmersionDerivedDirectImage
public import WeilII.Paper.ChainSectionPolynomial
public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.Cohomology

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The condition on a chain section over its field of definition in Zhang's proof of
Proposition 1.5, p. 4. Its polynomial zero scheme is smooth, and the compactly
supported cohomology of the open direct image vanishes outside the middle degree. -/
@[expose] public def HasRationalLefschetzChainSection {k : Type u} [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] {n : ℕ}
    (G : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) : Prop :=
  ∃ (a : Fin n → k) (c : k),
    let S := Spec (CommRingCat.of k)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ S).appTop).hom
    let p := MvPolynomial.eval₂Hom coeff (fun r : Fin n ↦ AffineSpace.coord S (ULift.up.{u} r))
      (chainSectionPolynomial a c)
    let i := X.zeroLocusSubschemeι {p}
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ S)
    let D := openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G
    IsSmoothAffineHypersurface i ∧
      ∀ e : ℤ, e ≠ (n : ℤ) → Subsingleton (D.compactlySupportedCohomology e).carrier

end WeilII
