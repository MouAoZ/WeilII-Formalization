module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Transport of natural linear duality along functor isomorphisms -/

open CategoryTheory Opposite

namespace WeilII
universe v w

/-- Pull a contravariantly natural linear duality back along a functor and transport both
sides along natural isomorphisms. -/
public theorem exists_natural_linearDual_of_iso
    {R : Type*} [CommRing R] {B C : Type*} [Category* B] [Category* C]
    (F : C ⥤ B) (H : B ⥤ ModuleCat.{v} R) (J : Bᵒᵖ ⥤ ModuleCat.{w} R)
    {A : C ⥤ ModuleCat.{v} R} {T : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (a : F ⋙ H ≅ A) (b : F.op ⋙ J ≅ T)
    (e : ∀ P, Module.Dual R (H.obj P) ≃ₗ[R] J.obj (op P))
    (he : ∀ {P P'} (f : P ⟶ P') (φ : Module.Dual R (H.obj P')),
      e P (φ.comp (H.map f).hom) = J.map f.op (e P' φ)) :
    ∃ d : ∀ M, Module.Dual R (A.obj M) ≃ₗ[R] T.obj (op M),
      ∀ {M M'} (f : M ⟶ M') (φ : Module.Dual R (A.obj M')),
        d M (φ.comp (A.map f).hom) = T.map f.op (d M' φ) := by
  refine ⟨fun M ↦ ((a.app M).toLinearEquiv.dualMap.trans (e (F.obj M))).trans
    (b.app (op M)).toLinearEquiv, ?_⟩
  intro M M' f φ
  have left : (φ.comp (A.map f).hom).comp (a.hom.app M).hom =
      (φ.comp (a.hom.app M').hom).comp (H.map (F.map f)).hom := by
    ext v
    exact congrArg φ (ConcreteCategory.congr_hom (a.hom.naturality f) v).symm
  change b.hom.app (op M) (e (F.obj M) ((φ.comp (A.map f).hom).comp (a.hom.app M).hom)) = _
  rw [left, he (F.map f)]
  exact ConcreteCategory.congr_hom (b.hom.naturality f.op) _

end WeilII
