module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient
public import WeilII.AlgebraicGeometry.BoundedOpenExchangeComponent

/-! # The compactification pasting on the underlying schemes -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar

private theorem paste_app {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {I : A ⥤ B} {P : B ⥤ C} {I' : A' ⥤ B'} {P' : B' ⥤ C'}
    {U : A ⥤ A'} {V : B ⥤ B'} {W : C ⥤ C'}
    (o : I ⋙ V ⟶ U ⋙ I') (p : P ⋙ W ⟶ V ⋙ P') (K : A) :
    ((Functor.associator I P W).hom ≫ Functor.whiskerLeft I p ≫ (Functor.associator I V P').inv ≫
      Functor.whiskerRight o P' ≫ (Functor.associator U I' P').hom).app K =
      p.app (I.obj K) ≫ P'.map (o.app K) := by simp

/-- The open/proper compactification exchange on the underlying derived complexes,
expressed using the scheme maps of the cartesian square. -/
public noncomputable def compactificationPastingOnSchemes
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U V U' V' : Scheme.{u}} {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'}
    (s : IsPullback x f' f y) (c : Compactification f) (K : residueExchangeDerived Λ U) :
    (rightDerivedLowerShriekOfCompactification Λ c ⋙ L((y)^*⟦Λ⟧)).obj K ⟶
      (L((x)^*⟦Λ⟧) ⋙ rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback s)).obj K :=
  let d := c.ofIsPullback s
  let J := D((c.i)_!open⟦Λ⟧)
  let J' := D((d.i)_!open⟦Λ⟧)
  let z := pullback.fst c.g y
  let θ := openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ
    (c.isPullback_i_ofIsPullback s).flip
  (residueExchangeBaseChange Λ (c.isPullback_g_ofIsPullback s).flip.toCommSq).app (J.obj K) ≫
    R((d.g)_*⟦Λ⟧).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ z).hom.app (J.obj K) ≫
      θ.hom.app K ≫ J'.map ((leftDerivedUpperStarIsoMapDerivedCategory Λ x).inv.app K))

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]

/-- On a bounded input, the compactification pasting first applies the ambient proper
exchange to the open extension. It then pushes forward the ambient open exchange,
written in the coordinates of the two derived pullbacks. -/
public theorem compactificationPasting_ambientComponent
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    (c : Compactification f.left) (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq).app K).hom =
      compactificationPastingOnSchemes (Profinite.padicAlgClRingObj ℓ) sq.overLeft c K.obj := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  let d := c.ofIsPullback sq.overLeft
  let J := D((c.i)_!open⟦Λ⟧)
  let J' := D((d.i)_!open⟦Λ⟧)
  let z := pullback.fst c.g y.left
  let θ := openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ
    (c.isPullback_i_ofIsPullback sq.overLeft).flip
  let i := c.overBaseChange_isPullback_i sq
  let p := c.overBaseChange_isPullback_g sq
  let Kc := (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI).obj K
  let e := (boundedConstructible _).ι.mapIso
    ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ i).app K)
  let h := (leftDerivedUpperStarIsoMapDerivedCategory Λ z).app (J.obj K.obj)
  let h' := J'.mapIso ((leftDerivedUpperStarIsoMapDerivedCategory Λ x.left).symm.app K.obj)
  have ho : e.inv = (h ≪≫ θ.app K.obj ≪≫ h').inv := by
    exact (boundedOpenExchange_inv_app_hom Λ ℓ i K).trans (Category.assoc h'.inv (θ.inv.app K.obj) h.inv).symm
  have he := congrArg Iso.hom (Iso.ext_inv ho)
  have hp : ((boundedConstructibleBaseChange ℓ p.toCommSq).app Kc).hom =
      (residueExchangeBaseChange Λ (c.isPullback_g_ofIsPullback sq.overLeft).flip.toCommSq).app
        (J.obj K.obj) := by
    have properComponent {X Y X' Y' : Over (Spec (.of k))}
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        {a : X ⟶ Y} {b : X' ⟶ Y'} {u : X' ⟶ X} {v : Y' ⟶ Y}
        (w : IsPullback u b a v) (M : Dᵇc(X.left)⟦Λ⟧) :
        ((boundedConstructibleBaseChange ℓ w.toCommSq).app M).hom =
          (residueExchangeBaseChange Λ w.overLeft.toCommSq).app M.obj := by
      have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
      have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
      have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
      have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
      have : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
      have : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
      have : LocallyOfFiniteType (X'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X'.hom›
      have : QuasiCompact (X'.left ↘ Spec (.of k)) := ‹QuasiCompact X'.hom›
      have : IsSeparated (X'.left ↘ Spec (.of k)) := ‹IsSeparated X'.hom›
      have : LocallyOfFiniteType (Y'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y'.hom›
      have : QuasiCompact (Y'.left ↘ Spec (.of k)) := ‹QuasiCompact Y'.hom›
      have : IsSeparated (Y'.left ↘ Spec (.of k)) := ‹IsSeparated Y'.hom›
      exact boundedConstructibleBaseChange_hom_eq_ambient ℓ k w.overLeft.toCommSq M
    exact properComponent p Kc
  have paste := congr_app (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq ℓ c sq) K
  have factors := paste_app (P := boundedConstructibleLowerStarOfIsProper ℓ c.overG)
    (P' := boundedConstructibleLowerStarOfIsProper ℓ d.overG)
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ i).hom
    (boundedConstructibleBaseChange ℓ p.toCommSq) K
  refine (congrArg (fun m ↦ m.hom) (paste.trans factors)).trans ?_
  exact congrArg₂ (· ≫ ·) hp (congrArg R((d.g)_*⟦Λ⟧).map he)

end WeilII
