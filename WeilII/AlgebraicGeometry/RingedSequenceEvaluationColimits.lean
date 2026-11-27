module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Colimits under vertical evaluation of module sheaves -/

public section
open CategoryTheory Limits Opposite WeilConjectures

namespace WeilII

universe s v u

/-- Vertical evaluation of modules on a ringed sequence site preserves all colimits in the
coefficient universe. The underlying abelian sheaves are restricted along the cocontinuous
inclusion of the slice, and the forgetful functor reflects colimits. -/
theorem ringedSequenceEvaluation_preservesColimits {C : Type u} [Category.{v} C]
    [EssentiallySmall.{s} C] (J : GrothendieckTopology C) (n : ℕ)
    [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
    [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{s}]
    [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{s}]
    [(Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    {R : Sheaf (coefficientSequenceTopology J) RingCat.{s}} {A : Sheaf J RingCat.{s}}
    (φ : A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) :
    PreservesColimitsOfSize.{s,s} (SheafOfModules.pushforward.{s} φ) := by
  let i := Prod.sectR n C
  let K := coefficientSequenceTopology J
  let H := i.sheafPushforwardContinuous AddCommGrpCat.{s} J K
  have : i.IsCocontinuous J K := ⟨fun h ↦ h⟩
  have : ∀ (P : Cᵒᵖ ⥤ AddCommGrpCat.{s}), i.op.HasPointwiseRightKanExtension P :=
    fun P X ↦ by
      let : HasLimitsOfShape (StructuredArrow X i.op) AddCommGrpCat.{s} :=
        HasLimitsOfShape.of_essentiallySmall _ _
      infer_instance
  have : PreservesColimitsOfSize.{s,s} H :=
    (i.sheafAdjunctionCocontinuous AddCommGrpCat.{s} J K).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{s,s} (SheafOfModules.toSheaf.{s} R) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  let U := SheafOfModules.toSheaf.{s} A
  have : PreservesColimitsOfSize.{s,s} U := ⟨fun {_} _ ↦ inferInstance⟩
  have : ReflectsColimitsOfSize.{s,s} U := reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{s,s} (SheafOfModules.pushforward.{s} φ ⋙ U) :=
    inferInstanceAs (PreservesColimitsOfSize.{s,s} (SheafOfModules.toSheaf.{s} R ⋙ H))
  exact preservesColimits_of_reflects_of_preserves _ U

end WeilII
