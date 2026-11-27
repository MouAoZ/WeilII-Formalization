module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Linear duality for a functor represented and corepresented at the tensor unit -/

open CategoryTheory MonoidalCategory Opposite

namespace WeilII

universe u v

/-- If maps from and to the tensor unit are detected bijectively by an additive functor
into modules, and the unit maps to the regular module, taking the internal dual into the
unit induces the linear dual under the functor, contravariantly naturally. -/
public theorem exists_natural_unitFiberDual
    {R : Type u} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
    {I : Cᵒᵖ ⥤ C ⥤ C} (adj : curriedTensor C ⊣₂ I)
    [∀ Q, ((curriedTensor C).obj Q).Additive]
    (H : C ⥤ ModuleCat.{v} R) [H.Additive] (i : H.obj (𝟙_ C) ≃ₗ[R] R)
    (outU : ∀ Q, Function.Bijective (H.map (X := 𝟙_ C) (Y := Q)))
    (intoU : ∀ Q, Function.Bijective (H.map (X := Q) (Y := 𝟙_ C))) :
    let D := I.flip.obj (𝟙_ C)
    ∃ e : ∀ Q, Module.Dual R (H.obj Q) ≃ₗ[R] H.obj (D.obj (op Q)),
      ∀ {P Q} (f : P ⟶ Q) (φ : Module.Dual R (H.obj Q)),
        e P (φ.comp (H.map f).hom) = H.map (D.map f.op) (e Q φ) := by
  classical
  intro D
  let U := 𝟙_ C
  let b (Q : C) : (U ⟶ Q) ≃ H.obj Q :=
    ((Equiv.ofBijective _ (outU Q)).trans ModuleCat.homEquiv).trans
      ((i.arrowCongr (LinearEquiv.refl R (H.obj Q))).toEquiv.trans
        (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv)
  let c (Q : C) : (Q ⟶ U) ≃ Module.Dual R (H.obj Q) :=
    ((Equiv.ofBijective _ (intoU Q)).trans ModuleCat.homEquiv).trans
      ((LinearEquiv.refl R (H.obj Q)).arrowCongr i).toEquiv
  have b_eq {Q} (f : U ⟶ Q) : b Q f = H.map f (i.symm 1) := rfl
  have c_eq {Q} (f : Q ⟶ U) : c Q f = i.toLinearMap.comp (H.map f).hom := rfl
  let j (Q : C) : (U ⟶ D.obj (op Q)) ≃ (Q ⟶ U) :=
    adj.homEquiv.symm.trans ((ρ_ Q).homCongr (Iso.refl U))
  have j_eq {Q} (f : U ⟶ D.obj (op Q)) : j Q f = (ρ_ Q).inv ≫ adj.homEquiv.symm f := by
    simp [j, Iso.homCongr_apply, U]
  have j_scalar {Q} (m : U ⟶ U) (f : U ⟶ D.obj (op Q)) : j Q (m ≫ f) = j Q f ≫ m := by
    rw [j_eq, adj.homEquiv_symm_naturality_two]
    change (ρ_ Q).inv ≫ Q ◁ m ≫ _ = _
    have E : adj.homEquiv.symm f = (ρ_ Q).hom ≫ j Q f := by simp [j_eq]
    rw [E, ← rightUnitor_naturality, ← Category.assoc (Q ◁ m), whisker_exchange,
      Category.assoc, ← unitors_equal, leftUnitor_naturality, unitors_equal,
      rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]
  let θ (Q : C) := (b (D.obj (op Q))).symm.trans ((j Q).trans (c Q))
  have eval {Q} (h : U ⟶ D.obj (op Q)) : θ Q (b _ h) = c Q (j Q h) := by simp [θ]
  let l (Q : C) : H.obj (D.obj (op Q)) ≃ₗ[R] Module.Dual R (H.obj Q) :=
    { θ Q with
      map_add' := by
        intro x y
        obtain ⟨h, rfl⟩ := (b _).surjective x
        obtain ⟨g, rfl⟩ := (b _).surjective y
        have hb : b _ (h + g) = b _ h + b _ g := by simp [b_eq, H.map_add]
        change θ Q (_ + _) = θ Q _ + θ Q _
        rw [← hb, eval, eval, eval]
        simp only [j_eq, ParametrizedAdjunction.homEquiv_eq, Adjunction.homAddEquiv_symm_add,
          Preadditive.comp_add, c_eq, H.map_add, ModuleCat.hom_add, LinearMap.comp_add]
      map_smul' := by
        intro a x
        obtain ⟨h, rfl⟩ := (b _).surjective x
        obtain ⟨m, hm⟩ := (outU U).surjective (ModuleCat.ofHom (a • LinearMap.id))
        have hb : b _ (m ≫ h) = a • b _ h := by simp [b_eq, H.map_comp, hm]
        change θ Q (a • _) = a • θ Q _
        rw [← hb, eval, eval, j_scalar, c_eq, c_eq, H.map_comp, hm]
        ext z
        simp }
  refine ⟨fun Q ↦ (l Q).symm, ?_⟩
  intro P Q f φ
  apply (l P).injective
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨h, hh⟩ := (b _).surjective ((l Q).symm φ)
  have hφ : φ = c Q (j Q h) := by
    rw [← eval]
    exact ((l Q).apply_symm_apply φ).symm.trans (congrArg (l Q) hh.symm)
  rw [← hh]
  have hb : H.map (D.map f.op) (b _ h) = b _ (h ≫ D.map f.op) := by simp [b_eq]
  rw [hb]
  change φ.comp (H.map f).hom = θ P _
  rw [eval, hφ]
  have hJ : j P (h ≫ D.map f.op) = f ≫ j Q h := by
    rw [j_eq, j_eq, ← Category.assoc, rightUnitor_inv_naturality, Category.assoc]
    exact congrArg ((ρ_ P).inv ≫ ·) (adj.homEquiv_symm_naturality_one f h)
  rw [hJ, c_eq, c_eq, H.map_comp]
  rfl

end WeilII
