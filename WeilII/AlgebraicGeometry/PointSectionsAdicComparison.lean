module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.TraceFormula.PointFiberFunctor
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace

/-! # Native and condensed global sections at a point -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Native adic global sections at a field agree as coefficient modules with sections
of the corresponding condensed module. Evaluation on the native unit represents a section
by a map out of that unit. Transport this map along the model equivalence and precompose
with the inverse unit comparison. Its scalar compatibility is the conjugation formula in
`CondensedModelScalar`, and its naturality follows from postcomposition. -/
public noncomputable def pointSectionsAdicComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] :
    adicGlobalSections ℓ (point k).left ≅
      (adicSheafEquivCondensedMod ℓ (point k).left).functor ⋙ pointSections ℓ k := by
  let s := (point k).left
  let A := adicSheafEquivCondensedMod ℓ s
  let U := AdicSheaf.unit ℓ s
  let uIso := adicSheafEquivCondensedModUnitIso ℓ s
  let Γ := adicGlobalSections ℓ s
  let S := pointSections ℓ k
  let ev (M : AdicSheaf ℓ s) : (U ⟶ M) ≃+ Γ.obj M :=
    AddEquiv.ofBijective (AddMonoidHom.mk' globalSectionOfModHom globalSectionOfModHom_add)
      (bijective_globalSectionOfModHom M)
  let sections (M : AdicSheaf ℓ s) : Γ.obj M ≃+ S.obj (A.functor.obj M) :=
    (ev M).symm.trans ((AddEquiv.mk' A.fullyFaithfulFunctor.homEquiv
      (fun _ _ ↦ A.functor.map_add)).trans
        (AddEquiv.mk' uIso.homFromEquiv (fun f g ↦ by
          change uIso.inv ≫ (f + g) = uIso.inv ≫ f + uIso.inv ≫ g
          exact Preadditive.comp_add ..)))
  have value (M : AdicSheaf ℓ s) (v : U ⟶ M) :
      sections M (globalSectionOfModHom v) = uIso.inv ≫ A.functor.map v := by
    change uIso.inv ≫ A.functor.map ((ev M).symm ((ev M) v)) = _
    rw [AddEquiv.symm_apply_apply]
  have linear (M : AdicSheaf ℓ s) (r : ULift.{u + 1} (PadicAlgCl ℓ)) (x : Γ.obj M) :
      sections M (r • x) = r • sections M x := by
    obtain ⟨v, rfl⟩ := (bijective_globalSectionOfModHom M).2 x
    have hv : r • globalSectionOfModHom v = globalSectionOfModHom (AdicSheaf.smul r U ≫ v) := by
      rw [AdicSheaf.smul_comp]
      exact (adicGlobalSectionOfHom_comp_smul v r.down).symm
    have hr : uIso.inv ≫ A.functor.map (AdicSheaf.smul r U) ≫ uIso.hom =
        (pointUnitEndRingHom ℓ k r.down).asHom :=
      adicSheafEquivCondensedModUnitIso_inv_comp_map_smul_comp_hom s r.down
    change sections M (r • globalSectionOfModHom v) =
      (pointUnitEndRingHom ℓ k r.down).asHom ≫ sections M (globalSectionOfModHom v)
    rw [hv, value, value, ← hr, Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  let e (M : AdicSheaf ℓ s) : Γ.obj M ≃ₗ[ULift.{u + 1} (PadicAlgCl ℓ)] S.obj (A.functor.obj M) :=
    { sections M with map_smul' := linear M }
  refine NatIso.ofComponents (fun M ↦ (e M).toModuleIso) ?_
  intro M N f
  ext x
  obtain ⟨v, rfl⟩ := (bijective_globalSectionOfModHom M).2 x
  change sections N ((Γ.map f) (globalSectionOfModHom v)) =
    sections M (globalSectionOfModHom v) ≫ A.functor.map f
  have hf : (Γ.map f) (globalSectionOfModHom v) = globalSectionOfModHom (v ≫ f) :=
    (globalSectionOfModHom_comp v f).symm
  rw [hf, value, value, Functor.map_comp, Category.assoc]

end WeilII
