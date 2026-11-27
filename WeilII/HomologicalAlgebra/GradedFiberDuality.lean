module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Transport of degree-zero duality to opposite cohomological degrees -/

open CategoryTheory Opposite

namespace WeilII

universe v

/-- For a contravariant duality that reverses shifts, a natural linear duality at degree
zero gives a natural linear duality between degrees `r` and `-r`. -/
public theorem exists_natural_gradedDual_of_zero
    {C : Type*} [Category* C] [HasShift C ℤ] {R : Type*} [CommRing R]
    (D : Cᵒᵖ ⥤ C) (H : ℤ → C ⥤ ModuleCat.{v} R) (r : ℤ)
    (shiftH : ∀ n, shiftFunctor C n ⋙ H 0 ≅ H n)
    (ds : (shiftFunctor C r).op ⋙ D ≅ D ⋙ shiftFunctor C (-r))
    (z : ∀ P, Module.Dual R ((H 0).obj P) ≃ₗ[R] (H 0).obj (D.obj (op P)))
    (hz : ∀ {P Q} (f : P ⟶ Q) (φ : Module.Dual R ((H 0).obj Q)),
      z P (φ.comp ((H 0).map f).hom) = (H 0).map (D.map f.op) (z Q φ)) :
    ∃ e : ∀ P, Module.Dual R ((H r).obj P) ≃ₗ[R] (H (-r)).obj (D.obj (op P)),
      ∀ {P Q} (f : P ⟶ Q) (φ : Module.Dual R ((H r).obj Q)),
        e P (φ.comp ((H r).map f).hom) = (H (-r)).map (D.map f.op) (e Q φ) := by
  let A := shiftFunctor C r
  let a : A ⋙ H 0 ≅ H r := shiftH r
  let b : A.op ⋙ D ⋙ H 0 ≅ D ⋙ H (-r) :=
    Functor.isoWhiskerRight ds (H 0) ≪≫ Functor.isoWhiskerLeft D (shiftH (-r))
  refine ⟨fun P ↦ ((a.app P).toLinearEquiv.dualMap.trans (z (A.obj P))).trans
    (b.app (op P)).toLinearEquiv, ?_⟩
  intro P Q f φ
  have hφ : (φ.comp ((H r).map f).hom).comp (a.hom.app P).hom =
      (φ.comp (a.hom.app Q).hom).comp ((H 0).map (A.map f)).hom := by
    ext x
    exact congrArg φ (ConcreteCategory.congr_hom (a.hom.naturality f) x).symm
  change b.hom.app (op P) (z (A.obj P) ((φ.comp ((H r).map f).hom).comp
    (a.hom.app P).hom)) = _
  rw [hφ]
  exact (congrArg (b.hom.app (op P)) (hz (A.map f) (φ.comp (a.hom.app Q).hom))).trans
    (ConcreteCategory.congr_hom (b.hom.naturality f.op) _)

end WeilII
