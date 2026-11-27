module

public import WeilII.AlgebraicGeometry.EtaleDualRootsOfUnityReductionTower
import Mathlib.RingTheory.PrincipalIdealDomain

open AlgebraicGeometry AlgebraicGeometry.Etale CategoryTheory

namespace WeilII

universe u

/-- Each transition of the dual Tate tower is epic. The unit for extension along the
coefficient quotient is the quotient of a sheaf by the kernel generator. Composing
that unit with the restriction of the finite Tate comparison preserves epicity. -/
public theorem etaleDualRootsOfUnityReductionEpi
    (S : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(S, ⊤))) (n : ℕ) :
    Epi ((etaleDualRootsOfUnityReductionTower S ℓ hℓ).map (homOfLE n.le_succ).op) := by
  let A (j : ℕ) := ZModCoeff.{u} (ℓ ^ (j + 1))
  let (j : ℕ) : NeZero (ringChar (A j)) :=
    ⟨by rw [ringChar.eq (A j) (ℓ ^ (j + 1))]; exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let (j : ℕ) : HasInvertibleExponent (A j) S :=
    ⟨ℓ ^ (j + 1), pow_pos (Fact.out : ℓ.Prime).pos _, ULift.ext (ZMod.natCast_self _),
      by simpa only [Nat.cast_pow] using hℓ.pow (j + 1)⟩
  let ρ : A (n + 1) →+* A n :=
    (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) _).ulift
  have hρ : Function.Surjective ρ := ULift.ringEquiv.symm.surjective.comp
    ((ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).comp ULift.ringEquiv.surjective)
  have : IsPrincipalIdealRing (A (n + 1)) := IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv.symm.toRingHom.comp (Int.castRingHom (ZMod (ℓ ^ (n + 2)))))
    (ULift.ringEquiv.symm.surjective.comp ZMod.intCast_surjective)
  let J := S.smallEtaleTopology
  let adj := Sheaf.extendScalarsAdjunction J ρ
  let D (j : ℕ) := tateTwistSheaf (A j) S (-1)
  let e := sheafExtendScalarsTateTwistSheafIso ρ S (-1)
  let U := sheafCompose J (forget₂ (ModuleCat.{u + 1} (A (n + 1))) AddCommGrpCat)
  change Epi ((Functor.ofOpSequence _).map _)
  erw [Functor.ofOpSequence_map_homOfLE_succ _ n]
  change Epi (U.map (adj.homEquiv _ _ e.hom))
  rw [Adjunction.homEquiv_unit]
  have : Epi (adj.unit.app (D (n + 1))) :=
    (Sheaf.extendScalarsReductionDatum J hρ
      (Submodule.IsPrincipal.span_singleton_generator (RingHom.ker ρ)).symm).epi_r _
  exact U.map_epi _

end WeilII
