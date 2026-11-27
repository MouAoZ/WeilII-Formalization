module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-! # The étale tower of duals of roots of unity

SGA 4, Exposé XVI, 3.10(a), p. 231 uses the dual of the sheaf of roots of unity.
The coefficient comparison is the one for finite Tate twists in
`WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist`. -/

open AlgebraicGeometry AlgebraicGeometry.Etale CategoryTheory

namespace WeilII

universe u

/-- The inverse system of dual root sheaves of SGA 4, XVI, 3.10(a).
At index `n` take the underlying abelian sheaf of the negative Tate line over
`ℤ/ℓ^(n+1)`. The successor map is adjoint to the scalar extension isomorphism of
that line along the coefficient quotient. In character coordinates it sends `χ` to
the character taking `z^ℓ` to the reduction of `χ(z)`. -/
@[expose] public noncomputable def etaleDualRootsOfUnityReductionTower
    (S : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  let A (n : ℕ) := ZModCoeff.{u} (ℓ ^ (n + 1))
  letI (n : ℕ) : NeZero (ringChar (A n)) :=
    ⟨by rw [ringChar.eq (A n) (ℓ ^ (n + 1))]; exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  letI (n : ℕ) : HasInvertibleExponent (A n) S :=
    ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _, ULift.ext (ZMod.natCast_self _),
      by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)⟩
  let D (n : ℕ) := tateTwistSheaf (A n) S (-1)
  let forgetLevel (n : ℕ) :=
    sheafCompose S.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} (A n)) AddCommGrpCat)
  Functor.ofOpSequence (X := fun n ↦ (forgetLevel n).obj (D n)) fun n ↦
    let ρ : A (n + 1) →+* A n :=
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))).ulift
    (forgetLevel (n + 1)).map <|
      (Sheaf.extendScalarsAdjunction S.smallEtaleTopology ρ).homEquiv (D (n + 1)) (D n)
        (sheafExtendScalarsTateTwistSheafIso ρ S (-1)).hom

end WeilII
