module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSingletonEvaluationMate
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence

/-! # Support of the derived singleton on the ringed sequence site -/

public section

open CategoryTheory Limits WeilConjectures.SemilinearSections

namespace WeilII

universe c v r
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in

/-- Derived evaluation on the sequence site has a left adjoint whose values vanish at all
strictly higher indices. Transport the strict singleton across the equivalence between strict
systems and modules on the sequence site, using its evaluation comparison at every index. -/
theorem semilinearSingleton_supportedAbove
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C] (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (n : ℕ) :
    ∃ L, Nonempty (L ⊣ e.{c, v, max c v r} J B τ n) ∧
      ∀ m, n < m → ∀ P, IsZero ((e.{c, v, max c v r} J B τ m).obj (L.obj P)) := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let scalars : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let coherence := SheafOfModules.systemTensorCoherence scalars
  let single := SheafOfModules.systemSingleDerivedExtension R n scalars coherence
  have (m : ℕ) : (evaluation.{c, v, max c v r} J B τ m).Additive := evaluationAdditive J B τ m
  have (m : ℕ) : PreservesFiniteLimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationLimits J B τ m
  have (m : ℕ) : PreservesFiniteColimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationColimits J B τ m
  let evaluationIso (m : ℕ) :
      E.inverse ⋙ SheafOfModules.systemEvaluation R m ≅ evaluation.{c, v, max c v r} J B τ m :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ m).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let derivedIso (m : ℕ) :
      E.mapDerivedCategory.inverse ⋙ SheafOfModules.derivedSystemEvaluation R m ≅
        e.{c, v, max c v r} J B τ m :=
    Functor.mapDerivedCategoryCompIso E.inverse (SheafOfModules.systemEvaluation R m) ≪≫
      Functor.mapDerivedCategoryNatIso (evaluationIso m)
  refine ⟨single.derived ⋙ E.mapDerivedCategory.functor,
    ⟨(single.adjunction.comp E.mapDerivedCategory.toAdjunction).ofNatIsoRight (derivedIso n)⟩, ?_⟩
  intro m hm P
  apply (SheafOfModules.systemSingleDerivedAbove scalars coherence R m n hm P).of_iso
  exact (derivedIso m).symm.app _ ≪≫ (SheafOfModules.derivedSystemEvaluation R m).mapIso
    (E.mapDerivedCategory.unitIso.symm.app (single.derived.obj P))

set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- On ringed systems the unit followed by the downward transition represents scalar extension.
The scalar adjoint transpose is the isomorphism of SemilinearSingletonEvaluationMate. -/
theorem semilinearSingleton_transition_bijective
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c v r} C] (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) {m n : ℕ} (h : m ≤ n)
    {L : D.{c, v, max c v r} J (B n) ⥤ DS.{c, v, max c v r} J B τ}
    (a : L ⊣ e.{c, v, max c v r} J B τ n) (P : D.{c, v, max c v r} J (B n))
    (N : D.{c, v, max c v r} J (B m)) :
    Function.Bijective fun g : (e.{c, v, max c v r} J B τ m).obj (L.obj P) ⟶ N ↦
      (a.unit.app P ≫ (derivedTransition.{c, v, max c v r} J B τ h).app (L.obj P)) ≫
        (resD.{c, v, max c v r} (coefficientMap J B τ h)).map g := by
  let φ := coefficientMap.{c, v, max c v r} J B τ h
  obtain ⟨A⟩ := (semilinearScalarData.{c, v, r} J (fun _ ↦ B n) (fun _ ↦ 𝟙 _)
    (fun _ ↦ B m) (fun _ ↦ 𝟙 _) (fun _ ↦ φ) (fun _ ↦ by simp)).2 0
  let k := A.T.map (a.unit.app P) ≫ reduction J B τ h A (L.obj P)
  have : IsIso k := semilinearSingletonEvaluationMate_isIso.{c, v, r} J B τ n m h A L a P
  have hk : A.adjunction.homEquiv _ _ k =
      a.unit.app P ≫ (derivedTransition J B τ h).app (L.obj P) := by
    rw [show k = _ from rfl, A.adjunction.homEquiv_naturality_left]
    exact congrArg (fun g ↦ a.unit.app P ≫ g) ((A.adjunction.homEquiv _ _).apply_symm_apply _)
  convert (A.adjunction.homEquiv P N).bijective.comp
    (asIso k).symm.homFromEquiv.bijective using 1
  funext g
  exact ((congrArg (fun f ↦ f ≫ _) hk.symm).trans
    (A.adjunction.homEquiv_naturality_right k g).symm)

/-- Both sides of the ordinary transition formula, as elements of the underlying
additive group of sections at the lower vertex. -/
theorem semilinearTransition_section {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{r} C] (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n, B (n+1) ⟶ B n)
    {m n : ℕ} (h : m ≤ n) (M : Systems.{c,v,r} J B τ) (U : C)
    (x : M.val.obj (Opposite.op (n,U))) :
    (show M.val.obj (Opposite.op (m,U)) from
      ((transition.{c,v,r} J B τ h).app M).val.app (Opposite.op U) x) =
    M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x := by
  exact congrFun (eq_of_heq ((transition_exists.{c,v,r} J B τ h).exists.choose_spec M
    (Opposite.op U))) x

end WeilII
