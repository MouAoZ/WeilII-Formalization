module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilII.HomologicalAlgebra.DegreeZeroFiberDuality
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.CategoryTheory.Triangulated.FullyFaithfulGenerator

/-! # Degree-zero duality for a fully faithful derived fiber over a field -/

open CategoryTheory MonoidalCategory Opposite

universe u

namespace WeilII

/-- If an additive fully faithful derived fiber sends the tensor unit to the regular field
in degree zero, degree-zero cohomology takes its internal dual to the linear dual. The
scalar field may be read through a ring equivalence in another universe. -/
public theorem exists_natural_derivedRegularFiberDual
    {R : Type*} [CommRing R] {S : Type u} [Field S] [HasDerivedCategory.{u} (ModuleCat.{u} S)]
    (ringIso : R ≃+* S)
    {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
    {I : Cᵒᵖ ⥤ C ⥤ C} (adj : curriedTensor C ⊣₂ I)
    [∀ Q, ((curriedTensor C).obj Q).Additive]
    (F : C ⥤ DerivedCategory (ModuleCat.{u} S)) [F.Additive] (ff : F.FullyFaithful)
    (eu : F.obj (𝟙_ C) ≅ (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of S S)) :
    let H := F ⋙ DerivedCategory.homologyFunctor _ 0 ⋙ ModuleCat.restrictScalars ringIso.toRingHom
    let D := I.flip.obj (𝟙_ C)
    ∃ e : ∀ P, Module.Dual R (H.obj P) ≃ₗ[R] H.obj (D.obj (op P)),
      ∀ {P Q} (f : P ⟶ Q) (φ : Module.Dual R (H.obj Q)),
        e P (φ.comp (H.map f).hom) = H.map (D.map f.op) (e Q φ) := by
  intro H D
  let U := 𝟙_ C
  let reg := ModuleCat.of S S
  let single := DerivedCategory.singleFunctor (ModuleCat S) 0
  let h0 := DerivedCategory.homologyFunctor (ModuleCat S) 0
  let res := ModuleCat.restrictScalars ringIso.toRingHom
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) 0).app reg
  let down : res.obj reg ≃ₗ[R] R :=
    { ringIso.symm.toEquiv with
      map_add' := ringIso.symm.map_add
      map_smul' := fun a x ↦ by
        change ringIso.symm (ringIso a * (show S from x)) = a * ringIso.symm x
        exact (ringIso.symm.map_mul (ringIso a) x).trans
          (congrArg (· * ringIso.symm x) (ringIso.symm_apply_apply a)) }
  let i : H.obj U ≃ₗ[R] R :=
    ((res.mapIso (h0.mapIso eu ≪≫ ε)).toLinearEquiv).trans down
  have : Module.Injective S S := Module.injective_of_isSemisimpleRing S S
  have : Injective reg := Module.injective_object_of_injective_module S S
  have outReg (Z) : h0.HomBijective (single.obj reg) Z := by
    let e := ε.symm.homCongr (Iso.refl (h0.obj Z))
    have he : (h0.map (X := single.obj reg) (Y := Z)) =
      e ∘ DerivedCategory.homSingleEquivOfProjective reg 0 Z := by
      funext f
      simp [e, Iso.homCongr_apply, DerivedCategory.homSingleToHomology, ε, h0]
    change Function.Bijective _
    rw [he]
    exact e.bijective.comp (DerivedCategory.homSingleEquivOfProjective reg 0 Z).bijective
  have intoReg (Z) : h0.HomBijective Z (single.obj reg) :=
    DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective Z reg
  let rf := Functor.FullyFaithful.ofFullyFaithful res
  have outU (Q) : Function.Bijective (H.map (X := U) (Y := Q)) :=
    (rf.map_bijective _ _).comp (((outReg _).of_iso_left eu.symm).comp (ff.map_bijective _ _))
  have intoU (Q) : Function.Bijective (H.map (X := Q) (Y := U)) :=
    (rf.map_bijective _ _).comp (((intoReg _).of_iso_right eu.symm).comp (ff.map_bijective _ _))
  exact exists_natural_unitFiberDual adj H i outU intoU

end WeilII
