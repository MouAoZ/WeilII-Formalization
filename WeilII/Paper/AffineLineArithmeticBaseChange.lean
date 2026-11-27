module

public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

import WeilII.Paper.AffineSpaceArithmeticBaseChange

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The two Weil sheaves obtained by changing the field of an arithmetic lisse sheaf on
the affine line are isomorphic. This is the coefficient identification in Zhang, §2,
p. 2, under the convention of finite extension of the field of definition.

Proof. Use the cartesian square for the affine line, and the isomorphism identifying
the geometric fibers over the two finite fields. Pulling E back successively to the
new arithmetic line and its geometric fiber gives its pullback along the composite.
The square identifies that composite with the map used to transport the original
geometric sheaf. The composition isomorphisms for adic inverse image thus identify the
carriers. For d the degree of the extension, the new geometric Frobenius corresponds
to the d-th iterate of the old one. The Weil isomorphism of a sheaf pulled back from
the arithmetic line is the comparison of pullbacks along Frobenius and the projection.
Pasting d such comparisons gives the comparison for the composite Frobenius by
functoriality of inverse image. Hence the carrier isomorphism intertwines the two
Weil structures and defines an isomorphism of constructible Weil sheaves. -/
public theorem affineLineArithmeticBaseChange_iso
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : ProEtale.AdicSheaf ℓ (affineLine k)) (hE : ProEtale.IsAdicLisseSheaf E) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    let f := AffineSpace.map PUnit.{u+1} (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let hK := ProEtale.IsAdicLisseSheaf.upperStar f hE
    Nonempty (affineSpaceWeilSheafBaseChangeField K (WeilSheaf.geometricFiberPullback (k₀ := k) hE) ≅
      WeilSheaf.geometricFiberPullback (k₀ := K) hK) := by
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  exact affineSpaceArithmeticBaseChange_iso (K := K) PUnit.{u+1} E hE

end WeilII
