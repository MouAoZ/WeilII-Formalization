module

public import WeilII.AlgebraicGeometry.FiniteProEtaleSystemPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData

/-! # Geometric direct and inverse images on the finite constant sequence site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open WeilConjectures
open CategoryTheory Limits Opposite AlgebraicGeometry WeilConjectures.SemilinearSections

namespace WeilII.FiniteProEtaleTowerGeometry

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime]

abbrev site (V : Scheme.{u}) := coefficientSequenceTopology (Scheme.ProEt.topology V)
abbrev tower (V : Scheme.{u}) := systemRing (Scheme.ProEt.topology V)
  (FiniteProEtaleSystem.rings ℓ V) (FiniteProEtaleSystem.steps ℓ V)
abbrev base {S T : Scheme.{u}} (f : S ⟶ T) := (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

instance {S T : Scheme.{u}} (f : S ⟶ T) : (base f).IsContinuous (site T) (site S) :=
  WeilConjectures.AmbientPullbackTensor.baseContinuous f none

attribute [local irreducible] Scheme.coefficientProEtaleDirectRingMap in
theorem levelNaturality {S T : Scheme.{u}} (f : S ⟶ T)
    {A B : CommRingCat.{u+1}} (q : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology T) _).map q ≫ Scheme.coefficientProEtaleDirectRingMap.{u,u} f B =
      Scheme.coefficientProEtaleDirectRingMap.{u,u} f A ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u+1}
          (Scheme.ProEt.topology T) (Scheme.ProEt.topology S)).map
          ((constantSheaf (Scheme.ProEt.topology S) _).map q) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u+1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj A) _).injective
  change (sheafificationAdjunction _ _).homEquiv _ _
    ((presheafToSheaf _ _).map ((Functor.const _).map q) ≫ _) = _
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold Scheme.coefficientProEtaleDirectRingMap
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congrArg (fun z ↦ z.app ((Scheme.proEtaleBaseChange f).op.obj V))
    ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{u+1}).unit.naturality
      ((Functor.const _).map q))

abbrev levels (V : Scheme.{u}) := rings (Scheme.ProEt.topology V)
  (FiniteProEtaleSystem.rings ℓ V) (FiniteProEtaleSystem.steps ℓ V)

/-- The canonical direct-image maps of constant rings, natural in the exponent. -/
def directLevels {S T : Scheme.{u}} (f : S ⟶ T) : levels ℓ T ⟶ levels ℓ S ⋙
    (Scheme.proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{u+1}
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology S) := by
  refine NatTrans.ofOpSequence (fun n ↦ Scheme.coefficientProEtaleDirectRingMap.{u,u} f
    (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n))) ?_
  intro n
  simpa only [levels, rings, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
    FiniteProEtaleSystem.steps] using levelNaturality f (CommRingCat.ofHom
      (Etale.FiniteProperQuotient.quotient ℓ (ULift.{u+1} ℚ_[ℓ]) n.le_succ))

/-- The direct-image coefficient map on the entire finite ring tower. For a product-site
arrow, horizontal naturality is naturality of `directLevels` and vertical naturality
is naturality of a single sheaf map. -/
def directRing {S T : Scheme.{u}} (f : S ⟶ T) : tower ℓ T ⟶
    ((base f).sheafPushforwardContinuous CommRingCat.{u+1} (site T) (site S)).obj (tower ℓ S) where
  hom :=
    { app := fun U ↦ ((directLevels ℓ f).app (op U.unop.1)).hom.app (op U.unop.2)
      naturality := by
        intro X Y g
        let p := g.unop.1.op
        let q := g.unop.2.op
        let d := directLevels ℓ f
        have h := congrArg (fun z ↦ z.hom.app (op X.unop.2)) (d.naturality p)
        have v := (d.app (op Y.unop.1)).hom.naturality q
        change ((levels ℓ T).map p).hom.app _ ≫ _ = _ ≫ _ at h
        change ((levels ℓ T).obj _).obj.map q ≫ _ = _ ≫ _ at v
        change (((levels ℓ T).map p).hom.app _ ≫ ((levels ℓ T).obj _).obj.map q) ≫ _ =
          _ ≫ (( (levels ℓ S).map p).hom.app _ ≫ _)
        rw [Category.assoc, v, ← Category.assoc, h, Category.assoc]
        rfl }

/-- Module direct image along the product-site base change. -/
def push {S T : Scheme.{u}} (f : S ⟶ T) :=
  SheafOfModules.pushforward.{u+1} (F := base f) (J := site T) (K := site S)
    (S := ring (site T) (tower ℓ T)) (R := ring (site S) (tower ℓ S))
    ⟨Functor.whiskerRight (directRing ℓ f).hom (forget₂ CommRingCat RingCat)⟩

instance {S T : Scheme.{u}} (f : S ⟶ T) : (push ℓ f).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u+1,u,u} _

/-- The left adjoint acts on the strict system of modules. -/
def pull {S T : Scheme.{u}} (f : S ⟶ T) := (push ℓ f).leftAdjoint

def adj {S T : Scheme.{u}} (f : S ⟶ T) : pull ℓ f ⊣ push ℓ f := Adjunction.ofIsRightAdjoint _

abbrev ev (V : Scheme.{u}) (n : ℕ) := evaluation.{u+1,u,u+1} (Scheme.ProEt.topology V)
  (FiniteProEtaleSystem.rings ℓ V) (FiniteProEtaleSystem.steps ℓ V) n

abbrev sliceId (V : Scheme.{u}) (n : ℕ) :=
  eqToHom (evaluation_ring.{u+1,u,u+1} (Scheme.ProEt.topology V)
    (FiniteProEtaleSystem.rings ℓ V) (FiniteProEtaleSystem.steps ℓ V) n).symm

theorem sliceId_app (V : Scheme.{u}) (n : ℕ) (U : V.ProEtᵒᵖ) :
    (sliceId ℓ V n).hom.app U = 𝟙 _ := by
  unfold sliceId
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

abbrev levelRing {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    ring _ (FiniteProEtaleSystem.rings ℓ T n) ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u+1}
        (Scheme.ProEt.topology T) (Scheme.ProEt.topology S)).obj
        (ring _ (FiniteProEtaleSystem.rings ℓ S n)) :=
  (sheafCompose _ (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
    (Scheme.coefficientProEtaleDirectRingMap.{u,u} f (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)))

abbrev towerRing {S T : Scheme.{u}} (f : S ⟶ T) :
    ring (site T) (tower ℓ T) ⟶
      ((base f).sheafPushforwardContinuous RingCat.{u+1} (site T) (site S)).obj
        (ring (site S) (tower ℓ S)) :=
  (sheafCompose _ (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map (directRing ℓ f)

/-- Evaluation of direct image at a vertex, in the ring-sheaf module model. Both
compositions restrict the scalars along the same map of sections. -/
def pushEval {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    push ℓ f ⋙ ev ℓ T n ≅ ev ℓ S n ⋙ Scheme.coefficientProEtaleModuleDirectImage.{u,u} f
      (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)) := by
  let g := Scheme.proEtaleBaseChange f
  let iT := Prod.sectR n T.ProEt
  let iS := Prod.sectR n S.ProEt
  let JT := Scheme.ProEt.topology T
  let JS := Scheme.ProEt.topology S
  have := Functor.isContinuous_comp iT (base f) JT (site T) (site S)
  have := Functor.isContinuous_comp g iS JT JS (site S)
  have h : sliceId ℓ T n ≫ (iT.sheafPushforwardContinuous RingCat JT (site T)).map
      (towerRing ℓ f) = levelRing ℓ f n ≫
        (g.sheafPushforwardContinuous RingCat JT JS).map (sliceId ℓ S n) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (sliceId ℓ T n).hom.app U ≫ (towerRing ℓ f).hom.app (op (n, U.unop)) =
      (levelRing ℓ f n).hom.app U ≫ (sliceId ℓ S n).hom.app (g.op.obj U)
    rw [sliceId_app, sliceId_app]
    rfl
  exact SheafOfModules.pushforwardComp (F := iT) (G := base f) (J := JT) (K := site T) (K' := site S)
      (sliceId ℓ T n) (towerRing ℓ f) ≪≫
    SheafOfModules.pushforwardCongr (F := iT ⋙ base f) (J := JT) (K := site S) h ≪≫
      (SheafOfModules.pushforwardComp (F := g) (G := iS) (J := JT) (K := JS) (K' := site S) (levelRing ℓ f n) (sliceId ℓ S n)).symm

abbrev levelAdj {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :=
  Scheme.coefficientProEtaleModuleAdjunction.{u,u} f
    (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n))

/-- Evaluating the inverse image of the sequence is the inverse image of the evaluated
module. The sequence-site mate theorem identifies the actual direct-image comparison. -/
def pullEval {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    pull ℓ f ⋙ ev ℓ S n ≅ ev ℓ T n ⋙ Scheme.coefficientProEtaleModulePullback.{u,u} f
      (CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)) := by
  have : IsIso ((mateEquiv (adj ℓ f) (levelAdj ℓ f n)).symm (pushEval ℓ f n).hom) :=
    WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology S) (Scheme.proEtaleBaseChange f)
      _ _ n (towerRing ℓ f) _ _ (evaluation_ring _ _ _ n) (evaluation_ring _ _ _ n) (levelRing ℓ f n) _ _
      (adj ℓ f) (levelAdj ℓ f n) (pushEval ℓ f n)
  exact (asIso ((mateEquiv (adj ℓ f) (levelAdj ℓ f n)).symm (pushEval ℓ f n).hom)).symm

/-- The inverse image on strict finite systems is additive and exact. Finite limits are
detected on the additive sections of the full product site, and pullback preserves them
on each vertex. Finite colimits are preserved by the adjunction. -/
theorem pull_exact {S T : Scheme.{u}} (f : S ⟶ T) :
    (pull ℓ f).Additive ∧ PreservesFiniteLimits (pull ℓ f) ∧ PreservesFiniteColimits (pull ℓ f) := by
  have : (push ℓ f).Additive := ⟨by intros; ext U x; rfl⟩
  have : PreservesColimitsOfSize.{0,0} (pull ℓ f) := (adj ℓ f).leftAdjoint_preservesColimits
  refine ⟨(adj ℓ f).left_adjoint_additive, ?_, inferInstance⟩
  have h (n : ℕ) : PreservesFiniteLimits (pull ℓ f ⋙ ev ℓ S n) := by
    let A := CommRingCat.of (FiniteProEtaleSystem.Coeff.{u} ℓ n)
    have : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback.{u,u} f A) :=
      (Scheme.coefficientProEtaleModulePullback_exact.{u,u} f A).1
    have := comp_preservesFiniteLimits (ev ℓ T n) (Scheme.coefficientProEtaleModulePullback.{u,u} f A)
    exact preservesFiniteLimits_of_natIso (pullEval ℓ f n).symm
  generalize he : pull ℓ f = F at h ⊢
  let R := ring (site S) (tower ℓ S)
  let U := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf _
  have : PreservesFiniteLimits (F ⋙ U) := by
    constructor
    intro I _ _
    apply preservesLimitsOfShape_of_evaluation
    intro V
    have := h V.unop.1
    let Rn := ring _ (FiniteProEtaleSystem.rings ℓ S V.unop.1)
    let Un := SheafOfModules.forget Rn ⋙ PresheafOfModules.toPresheaf _
    let e : (F ⋙ U) ⋙ (CategoryTheory.evaluation _ _).obj V ≅
        (F ⋙ ev ℓ S V.unop.1) ⋙ Un ⋙ (CategoryTheory.evaluation _ _).obj (op V.unop.2) :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
    exact preservesLimitsOfShape_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves F U

end WeilII.FiniteProEtaleTowerGeometry
