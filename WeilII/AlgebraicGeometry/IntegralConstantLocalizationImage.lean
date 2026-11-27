module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeValues
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived
import WeilII.AlgebraicGeometry.IntegralUniformizerMonoOnSubmodule

/-! # The localization unit on an elementary-divisor module -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The image of the integral localization unit on a direct sum of cyclic uniformizer-power
quotients and a free module is isomorphic to its free summand. Every map from a cyclic summand
to the restricted field module vanishes, while the unit embeds the finite free summand.
See SGA 4½, *Rapport*, §2.8. -/
public theorem nonempty_image_integralConstantModule_unit_iso_finiteFree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (V : Scheme.{u})
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (k r : ℕ) (e : Fin k → ℕ) :
    Nonempty (image ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield V ℓ E)).unit.app
        (integralConstantModule ℓ E.1 V π k r e)) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V) r) := by
  classical
  let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V
  have : @IsCommMonObj (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) _ _
      (sheafSymmetricCategory V).toBraidedCategory R inferInstance :=
    isCommMonObj_condensedRingObj _ _
  let w (n : ℕ) := padicIntegersRegularEndOfAlgebra V ℓ E.1 (π ^ n)
  let C (j : Fin k) := cokernel (w (e j))
  let T := ⨁ C
  let F := Mod.finiteFree R r
  let φ := padicIntegersToPadicSubfield V ℓ E
  let adj := Mod.extendRestrictAdjunction φ
  let L := Mod.extendScalars φ ⋙ Mod.comap φ
  let η := adj.unit.app (T ⊞ F)
  let B := L.obj (T ⊞ F)
  have hπB := mono_uniformizer_of_mono_into_restrictedFieldModule ℓ V E π hπ
    ((Mod.extendScalars φ).obj (T ⊞ F)) (𝟙 B)
  have hpow (n : ℕ) : Mono ((padicIntegersCenter V ℓ E.1 (π ^ n)).app B) := by
    change Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra V ℓ E.1 (π ^ n)) B)
    induction n with
    | zero =>
      rw [pow_zero, padicIntegersRegularEndOfAlgebra_one]
      erw [Mod.regularEndSMul_id (R := R) B]
      infer_instance
    | succ n ih =>
      rw [pow_succ, padicIntegersRegularEndOfAlgebra_mul]
      erw [Mod.regularEndSMul_comp (w n) (padicIntegersRegularEndOfAlgebra V ℓ E.1 π) B]
      have : Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra V ℓ E.1 π) B) := hπB
      exact mono_comp _ _
  have hcyc (j : Fin k) (g : C j ⟶ B) : g = 0 := by
    apply (cancel_epi (cokernel.π (w (e j)))).1
    rw [comp_zero]
    apply (cancel_mono ((padicIntegersCenter V ℓ E.1 (π ^ e j)).app B)).1
    rw [zero_comp, (padicIntegersCenter V ℓ E.1 (π ^ e j)).naturality]
    change Mod.regularEndSMul (w (e j)) _ ≫ cokernel.π (w (e j)) ≫ g = 0
    erw [Mod.regularEndSMul_unit (w (e j))]
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have ht : biprod.inl ≫ η = 0 := by
    apply biproduct.hom_ext'
    intro j
    exact (hcyc j _).trans (comp_zero.symm)
  have hf := mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers ℓ E V r
  have hn : biprod.inr ≫ η = adj.unit.app F ≫ L.map (biprod.inr : F ⟶ T ⊞ F) :=
    adj.unit.naturality _
  have : Mono (biprod.inr ≫ η) := by
    rw [hn]
    exact mono_comp _ _
  refine ⟨(image.isoStrongEpiMono (f := η) (biprod.snd : T ⊞ F ⟶ F) (biprod.inr ≫ η) ?_).symm⟩
  apply biprod.hom_ext'
  · simp only [biprod.inl_snd_assoc, zero_comp, ht]
  · simp only [biprod.inr_snd_assoc]

end WeilII
