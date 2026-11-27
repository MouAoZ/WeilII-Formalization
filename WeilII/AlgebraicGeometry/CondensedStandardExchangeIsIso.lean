module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange

/-! # Standard rational base change under a chosen pushforward-preservation proof -/

namespace WeilII

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

universe u

/-- Invertibility at a complex of the restricted exchange for a commutative square.
Keeping the coefficient ring explicit lets this criterion pass between its bundled and
unbundled presentations without expanding the restricted functors. -/
public structure IsInvertibleCondensedExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq v p' p g)
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards Λ k)
    (K : BoundedConstructible (condensedRingObj Λ X.left)) : Prop where
  /-- The exchange component is an isomorphism in the bounded constructible subcategory. -/
  isIso : IsIso ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ ℓ (@H) sq).app K)

/-- For algebraic-closure coefficients, any proof of preservation of bounded constructible
pushforwards gives the same exchange isomorphism criterion at a fixed input. The two maps
insert the same unit, transport through the same pullback square and contract the same counit.
The preservation witnesses are proof irrelevant. -/
public theorem isIso_condensedBaseChangeOfPreserves_of_standard
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq v p' p g)
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards (Profinite.padicAlgClRingObj ℓ) k)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (h : IsIso ((CondensedRing.boundedConstructibleBaseChange ℓ sq).app K)) :
    IsInvertibleCondensedExchange (Profinite.padicAlgClRingObj ℓ) ℓ k sq (@H) K := by
  constructor
  have heq : CondensedRing.boundedConstructibleBaseChangeOfPreserves
      (Profinite.padicAlgClRingObj ℓ) ℓ (@H) sq =
      CondensedRing.boundedConstructibleBaseChange ℓ sq := by
    rw [CondensedRing.boundedConstructibleBaseChange_def]
    with_unfolding_all rfl
  rw [heq]
  exact h

end WeilII
