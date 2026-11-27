module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange

/-! # The mate of a geometric adic pullback square -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- For every commutative square the mate of its pullback comparison is the canonical
adic base-change map. Taking a second mate identifies the conjugate of each pullback
composition and transport with its pushforward counterpart. -/
public theorem mate_adicUpperStarCompIso_eq_baseChangeMap
    (ℓ : ℕ) [Fact ℓ.Prime] {U' U T Y : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ T}
    {j : U ⟶ Y} {b : T ⟶ Y} (sq : CommSq a j' j b) :
    mateEquiv (adicUpperStarLowerStarAdjunction ℓ b) (adicUpperStarLowerStarAdjunction ℓ a)
      (TwoSquare.mk _ _ _ _ (adicUpperStarCompIso ℓ sq.w).hom) = adicBaseChangeMap ℓ sq := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction ℓ j')
    (adicUpperStarLowerStarAdjunction ℓ j)).injective
  rw [adicBaseChangeMap, Equiv.apply_symm_apply, iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv _ _
    ((adicUpperStarComp ℓ a j).inv ≫ (adicUpperStarCongr ℓ sq.w).hom ≫
      (adicUpperStarComp ℓ j' b).hom) = _
  rw [← Category.assoc,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction ℓ (j' ≫ b)),
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction ℓ (a ≫ j)),
    conjugateEquiv_adicUpperStarComp_hom, conjugateEquiv_adicUpperStarComp_inv]
  have transport : (adicUpperStarCongr ℓ sq.w).hom =
      (adicUpperStarCongr ℓ sq.w.symm).inv := rfl
  rw [transport, conjugateEquiv_adicUpperStarCongr_inv]
  rfl

end WeilII
