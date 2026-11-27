module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Detecting isomorphisms of sheaves of module diagrams

Mathlib's `PresheafOfModules.isoMk` constructs inverses from vertexwise linear isomorphisms.
We apply it to sheaves valued in modules over a diagram of rings, as used for the finite
quotient systems before (†) on page 2 of Zhang. -/

public section

namespace WeilII

open CategoryTheory Opposite

/-- Evaluation at a surjective family of vertices jointly detects isomorphisms of sheaves
valued in modules over a diagram of rings. Evaluate a sheaf morphism at a test object.
At each vertex its component is an isomorphism by the hypothesis on the evaluated sheaves.
The component inverses are natural by `PresheafOfModules.isoMk`. The resulting isomorphism
on every test object makes the underlying presheaf map invertible, and the fully faithful
inclusion of sheaves reflects this property. Source: Mathlib, `ModuleCat.Presheaf` and
`CategoryTheory.Sites.Whiskering`. -/
theorem sheafModuleDiagramEvaluation_jointlyReflects
    {C I : Type*} [Category* C] [Category* I] (J : GrothendieckTopology C)
    (R : Iᵒᵖ ⥤ RingCat.{w}) {ι : Type*} (j : ι → Iᵒᵖ) (hj : Function.Surjective j)
    [∀ n, J.HasSheafCompose (PresheafOfModules.evaluation.{w} R (j n))] :
    JointlyReflectIsomorphisms (fun n ↦ sheafCompose J (PresheafOfModules.evaluation.{w} R (j n))) := by
  constructor
  intro X Y f hf
  rw [← isIso_iff_of_reflects_iso f (sheafToPresheaf J _), NatTrans.isIso_iff_isIso_app]
  intro U
  have hv (i : Iᵒᵖ) : IsIso ((f.hom.app U).app i) := by
    obtain ⟨n, rfl⟩ := hj i
    exact ((sheafToPresheaf J _ ⋙ (evaluation _ _).obj U).mapIso
      (asIso ((sheafCompose J (PresheafOfModules.evaluation.{w} R (j n))).map f))).isIso_hom
  let e := PresheafOfModules.isoMk (fun i ↦ asIso ((f.hom.app U).app i))
    (fun {_ _} a ↦ (f.hom.app U).naturality a)
  exact e.isIso_hom

end WeilII
