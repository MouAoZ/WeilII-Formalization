module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSingletonEvaluationMate
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStar
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsSquare
import WeilII.AlgebraicGeometry.ClosedDirectImageRestrictionMate
import WeilII.AlgebraicGeometry.SemilinearSingletonSupport
import WeilII.AlgebraicGeometry.SingletonEvaluationComparison
import WeilII.AlgebraicGeometry.SingletonTransitionCoordinates
import WeilII.AlgebraicGeometry.RingedSequenceEvaluationColimits
public import WeilII.AlgebraicGeometry.DerivedTransitionMate
import WeilII.AlgebraicGeometry.DerivedTransitionMateComponents

/-! # Closed support on the étale system of finite quotient rings

The system category and its transitions are those of WeilConjectures'
`SemilinearSystemModels`. The finite-level right adjoint uses the proper comparison
and the adjunction of `Etale.Derived.UpperShriek`. This is the closed-immersion
calculation needed for the coefficient tower in Zhang, §2. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor

namespace WeilII.EtaleQuotientSystem

universe u
variable (ℓ : ℕ)

/-- The coefficient at index `n` is the positive-power quotient of exponent `n+1`. -/
abbrev Coeff (n : ℕ) := ULift.{u+1} (ZMod (ℓ ^ (n+1)))

/-- The map of finite rings taking a residue class to its class modulo the lower power. -/
def quotient {a b : ℕ} (h : a ≤ b) : Coeff.{u} ℓ b →+* Coeff.{u} ℓ a :=
  ULift.ringEquiv.symm.toRingHom.comp ((ZMod.castHom
    (pow_dvd_pow ℓ (Nat.add_le_add_right h 1)) _).comp ULift.ringEquiv.toRingHom)

/-- The constant commutative ring sheaf of the indicated quotient. -/
abbrev rings (V : Scheme.{u}) (n : ℕ) :=
  (constantSheaf V.smallEtaleTopology CommRingCat.{u+1}).obj (CommRingCat.of (Coeff.{u} ℓ n))

/-- The adjacent ring maps of the sequence site are the sheafified residue maps. -/
def steps (V : Scheme.{u}) (n : ℕ) : rings ℓ V (n+1) ⟶ rings ℓ V n :=
  (constantSheaf V.smallEtaleTopology CommRingCat.{u+1}).map
    (CommRingCat.ofHom (quotient.{u} ℓ n.le_succ))

/-- Ordinary strict systems, as module sheaves on the ringed sequence site. -/
abbrev Systems (V : Scheme.{u}) :=
  SemilinearSections.Systems V.smallEtaleTopology (rings ℓ V) (steps ℓ V)

/-- The unbounded derived category of the strict systems. -/
abbrev DS (V : Scheme.{u}) :=
  SemilinearSections.DS V.smallEtaleTopology (rings ℓ V) (steps ℓ V)

/-- Forget commutativity on the sequence-site ring of SemilinearSystemModels. -/
abbrev systemRing (V : Scheme.{u}) :=
  SemilinearSections.ring _ (SemilinearSections.systemRing V.smallEtaleTopology (rings ℓ V) (steps ℓ V))

/-- Evaluation as a sheaf of modules over a fixed residue ring. After ordinary
ringed-site evaluation, restrict the action to constant sections using the
constant-ring comparison and the étale constant-module equivalence. -/
def eval (V : Scheme.{u}) (n : ℕ) :
    Systems ℓ V ⥤ Sheaf V.smallEtaleTopology (ModuleCat.{u+1} (Coeff.{u} ℓ n)) :=
  SemilinearSections.evaluation _ (rings ℓ V) (steps ℓ V) n ⋙
    SheafOfModules.restrictScalars (realizationRingIso V.smallEtaleTopology (Coeff ℓ n)).inv ⋙
      V.etaleConstantModuleRestrictionFunctor (Coeff ℓ n)

/-- Evaluation and restriction of scalars both add maps sectionwise. -/
instance (V : Scheme.{u}) (n : ℕ) : (eval ℓ V n).Additive where
  map_add := by intros; ext U x; rfl

/-- Restriction of scalars preserves finite limits and colimits because the underlying
abelian sheaf functor preserves and reflects them (SemilinearSystemModels, res_exact). -/
private theorem scalarRestrictionExact {V : Scheme.{u}} {A B : Sheaf V.smallEtaleTopology RingCat.{u+1}}
    (φ : A ⟶ B) : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u+1} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u+1} φ) := by
  let F := SheafOfModules.restrictScalars.{u+1} φ
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf B))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf A)⟩

/-- The constant-ring restriction functor has the explicit unit and counit of
EtaleConstantRingModuleEquivalence. -/
private instance fixedEquivalence (V : Scheme.{u}) (A : Type (u+1)) [CommRing A] :
    (V.etaleConstantModuleRestrictionFunctor A).IsEquivalence :=
  Functor.IsEquivalence.mk' (V.etaleConstantModuleFunctor A)
    (V.etaleConstantModuleCounitIso A).symm (V.etaleConstantModuleUnitIso A).symm

/-- Left exactness follows from ringed evaluation and exact scalar restriction. -/
instance (V : Scheme.{u}) (n : ℕ) : PreservesFiniteLimits (eval ℓ V n) := by
  unfold eval
  have := (scalarRestrictionExact (V := V) (realizationRingIso _ (Coeff ℓ n)).inv).1
  infer_instance

/-- Cokernels of systems are computed at each level, and constant-ring restriction
preserves them. -/
instance (V : Scheme.{u}) (n : ℕ) : PreservesFiniteColimits (eval ℓ V n) := by
  unfold eval
  have := (scalarRestrictionExact (V := V) (realizationRingIso _ (Coeff ℓ n)).inv).2
  infer_instance

/-- Derived evaluation from the localization of strict systems to the usual finite
étale derived category. -/
abbrev ev (V : Scheme.{u}) (n : ℕ) : DS ℓ V ⥤ Etale.DerivedCategoryModule (Coeff ℓ n) V :=
  (eval ℓ V n).mapDerivedCategory

/-- The site functor for the direct image of strict systems. -/
abbrev baseChange {S T : Scheme.{u}} (d : S ⟶ T) : (ℕ × T.Etale) ⥤ (ℕ × S.Etale) :=
  (𝟭 ℕ).prod (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ d)

/-- The residue map regarded as ordinary restriction of module-valued sheaves. -/
abbrev restrict (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b) :=
  Sheaf.restrictScalars V.smallEtaleTopology (quotient.{u} ℓ h)

/-- A finite-coefficient presentation of the actual transition. Its value on
each section is the horizontal restriction of the original system. -/
def IsTransition (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (t : eval ℓ V b ⟶ eval ℓ V a ⋙ restrict ℓ V h) : Prop :=
  ∀ (M : Systems ℓ V) (U : V.Etale) (x : M.val.obj (op (b, U))),
    let y : M.val.obj (op (a, U)) := (t.app M).hom.app (op U) x
    y = M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x

/-- Localize an ordinary transition exactly as in SemilinearSections.derivedTransition,
in the module-valued coordinates. -/
def transitionD (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (t : eval ℓ V b ⟶ eval ℓ V a ⋙ restrict ℓ V h) :
    ev ℓ V b ⟶ ev ℓ V a ⋙ Sheaf.derivedRestrictScalars V.smallEtaleTopology (quotient ℓ h) :=
  Functor.mapDerivedCategoryNatTrans t ≫
    (Functor.mapDerivedCategoryCompIso (eval ℓ V a) (restrict ℓ V h)).inv

/-- The ordinary étale direct image at one quotient, as in Etale.lowerStar. -/
abbrev push {S T : Scheme.{u}} (d : S ⟶ T) (n : ℕ) :=
  Etale.lowerStar (ModuleCat.{u+1} (Coeff ℓ n)) d

variable [Fact ℓ.Prime] {S T : Scheme.{u}} (d : S ⟶ T) [IsClosedImmersion d]

/-- The finite adjunction, with its left side identified using properness and
exactness of closed direct image. -/
def supportAdjunction (n : ℕ) :
    (push ℓ d n).mapDerivedCategory ⊣ Etale.rightDerivedUpperShriek (Coeff ℓ n) d :=
  (Etale.rightDerivedUpperShriekAdjunction (Coeff ℓ n) d).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ d ≪≫
      (push ℓ d n).rightDerivedFunctorIsoMapDerivedCategory)

/-- The comparison from restriction after support to support after restriction.
It is the mate of the identity on the underlying sections of closed direct image. -/
def supportRestriction {a b : ℕ} (h : a ≤ b) :
    Etale.rightDerivedUpperShriek (Coeff ℓ a) d ⋙
        Sheaf.derivedRestrictScalars S.smallEtaleTopology (quotient ℓ h) ⟶
      Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient ℓ h) ⋙
        Etale.rightDerivedUpperShriek (Coeff ℓ b) d :=
  let c := Functor.mapDerivedCategorySquareIso
    (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).symm
  mateEquiv (supportAdjunction ℓ d a) (supportAdjunction ℓ d b) (TwoSquare.mk _ _ _ _ c.hom)

/-- The map between the rings on the sequence sites is fixed by its action on
constant sections at every exponent. -/
def PreservesConstants
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1}
      _ _).obj (systemRing ℓ S)) : Prop :=
  ∀ (n : ℕ) (U : T.Etale) (c : Coeff.{u} ℓ n),
    φ.hom.app (op (n, U)) ((realizationRingUnit T.smallEtaleTopology (Coeff ℓ n)).app (op U) c) =
      (realizationRingUnit S.smallEtaleTopology (Coeff ℓ n)).app
        (op (((baseChange d).obj (n, U)).2)) c

/-- Localization of an exact functor between the two ringed sequence sites. -/
abbrev pushD (F : Systems ℓ S ⥤ Systems ℓ T) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : DS ℓ S ⥤ DS ℓ T :=
  F.mapDerivedCategory

/-- The evaluation comparison is the mate of the sectionwise identification for
closed direct image. The two adjunctions thus prescribe its counit formula. -/
def supportEvaluation (F : Systems ℓ S ⥤ Systems ℓ T) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {D : DS ℓ T ⥤ DS ℓ S} (adj : pushD ℓ F ⊣ D) (n : ℕ)
    (v : F ⋙ eval ℓ T n ≅ eval ℓ S n ⋙ push ℓ d n) :
    D ⋙ ev ℓ S n ⟶ ev ℓ T n ⋙ Etale.rightDerivedUpperShriek (Coeff ℓ n) d :=
  let c : pushD ℓ F ⋙ ev ℓ T n ≅ ev ℓ S n ⋙ (push ℓ d n).mapDerivedCategory :=
    Functor.mapDerivedCategorySquareIso v
  mateEquiv adj (supportAdjunction ℓ d n) (TwoSquare.mk _ _ _ _ c.inv)

/-- Every coefficient in a lifted residue ring is the image of an integer. -/
theorem coefficient_intCast_surjective (n : ℕ) (c : Coeff.{u} ℓ n) : ∃ k : ℤ, (k : Coeff ℓ n) = c := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective c.down
  exact ⟨k, ULift.ext hk⟩

private theorem coefficientMap_exists :
    ∃ hc : (baseChange d).IsContinuous (coefficientSequenceTopology T.smallEtaleTopology)
        (coefficientSequenceTopology S.smallEtaleTopology),
    letI := hc
    ∃ φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1}
        _ _).obj (systemRing ℓ S),
      PreservesConstants ℓ d φ := by
  classical
  let B := d.Etale
  have hc : (baseChange d).IsContinuous (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology) := by
    have : RepresentablyFlat B := d.representablyFlat_etale
    have : RepresentablyFlat (baseChange d) :=
      ⟨fun U ↦ IsCofiltered.of_equivalence (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) B).symm⟩
    apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    constructor
    intro U R hR
    change (R.functorPushforward (baseChange d)).functorPullback (Prod.sectR U.1 S.Etale) ∈
      S.smallEtaleTopology (B.obj U.2)
    apply S.smallEtaleTopology.superset_covering _
      (d.coverPreserving_etale.cover_preserve hR)
    intro V a ha
    obtain ⟨W, g, h, hg, rfl⟩ := ha
    exact ⟨(U.1, W), Prod.mkHom (𝟙 U.1) g, Prod.mkHom (𝟙 U.1) h, hg, by
      ext <;> simp [baseChange] <;> rfl⟩
  refine ⟨hc, ?_⟩
  let P := B.sheafPushforwardContinuous CommRingCat.{u+1} T.smallEtaleTopology S.smallEtaleTopology
  let cmp (A : CommRingCat.{u+1}) :
      (constantSheaf T.smallEtaleTopology _).obj A ⟶
        P.obj ((constantSheaf S.smallEtaleTopology _).obj A) :=
    ((sheafificationAdjunction T.smallEtaleTopology _).homEquiv _ _).symm
      (Functor.whiskerLeft B.op (toSheafify S.smallEtaleTopology ((Functor.const _).obj A)))
  have cmp_nat {A A' : CommRingCat.{u+1}} (f : A ⟶ A') :
      (constantSheaf T.smallEtaleTopology _).map f ≫ cmp A' =
        cmp A ≫ P.map ((constantSheaf S.smallEtaleTopology _).map f) := by
    apply ((sheafificationAdjunction T.smallEtaleTopology CommRingCat.{u+1}).homEquiv
      ((Functor.const _).obj A) _).injective
    change ((sheafificationAdjunction T.smallEtaleTopology _).homEquiv _ _)
      ((presheafToSheaf _ _).map ((Functor.const _).map f) ≫ _) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [cmp, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    exact congrArg (fun t ↦ t.app (B.op.obj U))
      ((toSheafification S.smallEtaleTopology CommRingCat.{u+1}).naturality ((Functor.const _).map f))
  let δ : SemilinearSections.rings _ (rings ℓ T) (steps ℓ T) ⟶
      SemilinearSections.rings _ (rings ℓ S) (steps ℓ S) ⋙ P :=
    NatTrans.ofOpSequence (fun n ↦ cmp (CommRingCat.of (Coeff ℓ n))) (fun n ↦ by
      simpa only [steps, SemilinearSections.rings, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
        using cmp_nat (CommRingCat.ofHom (quotient.{u} ℓ n.le_succ)))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := T.Etale)).functor
    (Functor.uncurry.map (Functor.whiskerRight δ (sheafToPresheaf _ _)))
  let φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1}
      _ _).obj (systemRing ℓ S) :=
    ⟨{ app := fun U ↦ (forget₂ CommRingCat RingCat).map
         ((cmp (CommRingCat.of (Coeff ℓ U.unop.1))).hom.app (op U.unop.2))
       naturality := fun _ _ a ↦ (forget₂ CommRingCat RingCat).congr_map (ε.naturality a) }⟩
  refine ⟨φ, ?_⟩
  intro n U c
  obtain ⟨k, rfl⟩ := coefficient_intCast_surjective ℓ n c
  simp only [map_intCast]

/-- Reading a fixed-coefficient evaluation on a test object recovers the underlying additive group of sections. -/
def evalSections (V : Scheme.{u}) (n : ℕ) (M : Systems ℓ V) (U : V.Etaleᵒᵖ) :
    ((eval ℓ V n).obj M).obj.obj U ≃+ M.val.obj (op (n, U.unop)) := AddEquiv.refl _

private def restrictedSections (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (M : Systems ℓ V) (U : V.Etaleᵒᵖ) :
    ((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.obj U ≃+ M.val.obj (op (a, U.unop)) :=
  evalSections ℓ V a M U

private def liftAdditive (n : ℕ) (A B : ModuleCat.{u+1} (Coeff.{u} ℓ n)) (f : A →+ B) : A ⟶ B := by
  refine ModuleCat.ofHom { __ := f, map_smul' := ?_ }
  intro c x
  obtain ⟨k, rfl⟩ := coefficient_intCast_surjective ℓ n c
  simp only [RingHom.id_apply, Int.cast_smul_eq_zsmul]
  exact map_zsmul f k x

private def transitionSection (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (M : Systems ℓ V) (U : V.Etaleᵒᵖ) :
    ((eval ℓ V b).obj M).obj.obj U ⟶ ((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.obj U := by
  let f := ((restrictedSections ℓ V h M U).symm.toAddMonoidHom.comp
    (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom).comp
      (evalSections ℓ V b M U).toAddMonoidHom
  exact liftAdditive ℓ b _ _ f

private theorem transitionSection_apply (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (M : Systems ℓ V) (U : V.Etaleᵒᵖ) (x : ((eval ℓ V b).obj M).obj.obj U) :
    restrictedSections ℓ V h M U (transitionSection ℓ V h M U x) =
      M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op (evalSections ℓ V b M U x) := rfl

private theorem evalSections_map (V : Scheme.{u}) (n : ℕ) (M : Systems ℓ V)
    {U W : V.Etaleᵒᵖ} (f : U ⟶ W) (x : ((eval ℓ V n).obj M).obj.obj U) :
    evalSections ℓ V n M W (((eval ℓ V n).obj M).obj.map f x) =
      M.val.presheaf.map (Prod.mkHom (𝟙 n) f.unop).op (evalSections ℓ V n M U x) := rfl

private theorem restrictedSections_map (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b) (M : Systems ℓ V)
    {U W : V.Etaleᵒᵖ} (f : U ⟶ W) (x : ((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.obj U) :
    restrictedSections ℓ V h M W (((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.map f x) =
      M.val.presheaf.map (Prod.mkHom (𝟙 a) f.unop).op (restrictedSections ℓ V h M U x) := rfl

private theorem transitionSection_naturality (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    (M : Systems ℓ V) {U W : V.Etaleᵒᵖ} (f : U ⟶ W) :
    ((eval ℓ V b).obj M).obj.map f ≫ transitionSection ℓ V h M W =
      transitionSection ℓ V h M U ≫ ((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let i : op (b,U.unop) ⟶ op (b,W.unop) := (Prod.mkHom (𝟙 b) f.unop).op
  let j : op (b,W.unop) ⟶ op (a,W.unop) := (Prod.mkHom (homOfLE h) (𝟙 W.unop)).op
  let i' : op (b,U.unop) ⟶ op (a,U.unop) := (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  let j' : op (a,U.unop) ⟶ op (a,W.unop) := (Prod.mkHom (𝟙 a) f.unop).op
  have comm : i ≫ j = i' ≫ j' := by apply Quiver.Hom.unop_inj; ext <;> simp [i,j,i',j']
  apply (restrictedSections ℓ V h M W).injective
  simp only [ModuleCat.comp_apply, transitionSection_apply, evalSections_map, restrictedSections_map]
  exact (M.val.map_comp_apply i j (evalSections ℓ V b M U x)).symm.trans
    ((M.val.congr_map_apply comm _).trans (M.val.map_comp_apply i' j' _))

private def transitionAt (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b) (M : Systems ℓ V) :
    (eval ℓ V b).obj M ⟶ (eval ℓ V a ⋙ restrict ℓ V h).obj M :=
  ⟨{ app := transitionSection ℓ V h M, naturality := fun {_ _} f ↦ transitionSection_naturality ℓ V h M f }⟩

private theorem evalSections_morphism (V : Scheme.{u}) (n : ℕ) {M N : Systems ℓ V}
    (f : M ⟶ N) (U : V.Etaleᵒᵖ) (x : ((eval ℓ V n).obj M).obj.obj U) :
    evalSections ℓ V n N U (((eval ℓ V n).map f).hom.app U x) =
      f.val.app (op (n, U.unop)) (evalSections ℓ V n M U x) := rfl

private theorem restrictedSections_morphism (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b)
    {M N : Systems ℓ V} (f : M ⟶ N) (U : V.Etaleᵒᵖ)
    (x : ((eval ℓ V a ⋙ restrict ℓ V h).obj M).obj.obj U) :
    restrictedSections ℓ V h N U (((eval ℓ V a ⋙ restrict ℓ V h).map f).hom.app U x) =
      f.val.app (op (a, U.unop)) (restrictedSections ℓ V h M U x) := rfl

private def systemTransition (V : Scheme.{u}) {a b : ℕ} (h : a ≤ b) :
    eval ℓ V b ⟶ eval ℓ V a ⋙ restrict ℓ V h := by
  let t : eval ℓ V b ⟶ eval ℓ V a ⋙ restrict ℓ V h :=
    { app := transitionAt ℓ V h
      naturality := fun {M N} f ↦ by
        ext U x
        apply (restrictedSections ℓ V h N U).injective
        change restrictedSections ℓ V h N U
            (transitionSection ℓ V h N U (((eval ℓ V b).map f).hom.app U x)) =
          restrictedSections ℓ V h N U
            (((eval ℓ V a ⋙ restrict ℓ V h).map f).hom.app U (transitionSection ℓ V h M U x))
        rw [transitionSection_apply, evalSections_morphism, restrictedSections_morphism,
          transitionSection_apply]
        exact (PresheafOfModules.naturality_apply f.val
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op (evalSections ℓ V b M U x)).symm }
  exact t


/-- Closed direct image of ordinary systems along a map of coefficient sheaves. -/
abbrev systemPush
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) : Systems ℓ S ⥤ Systems ℓ T := SheafOfModules.pushforward φ

/-- An evaluation comparison at every level of an ordinary system functor. -/
abbrev EvalSquares (F : Systems ℓ S ⥤ Systems ℓ T) :=
  ∀ n, F ⋙ eval ℓ T n ≅ eval ℓ S n ⋙ push ℓ d n

set_option cleanup.letToHave false in
/-- The natural comparison induced by the identity on sections over each base-changed test object. -/
def systemPushEvaluations
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) :
    let F := systemPush ℓ d φ
    EvalSquares ℓ d F := by
  let F := systemPush ℓ d φ
  let liftIso (n : ℕ) (A A' : ModuleCat.{u+1} (Coeff.{u} ℓ n)) (e : A ≃+ A') : A ≅ A' :=
    LinearEquiv.toModuleIso
      { __ := e
        map_smul' := fun c x ↦ by
          obtain ⟨k, rfl⟩ := coefficient_intCast_surjective ℓ n c
          simp only [RingHom.id_apply, Int.cast_smul_eq_zsmul]
          exact map_zsmul e k x }
  let component (n : ℕ) (M : Systems ℓ S) (U : T.Etaleᵒᵖ) :
      ((F ⋙ eval ℓ T n).obj M).obj.obj U ≅ ((eval ℓ S n ⋙ push ℓ d n).obj M).obj.obj U :=
    liftIso n _ _ ((evalSections ℓ T n (F.obj M) U).trans
      (evalSections ℓ S n M (d.Etale.op.obj U)).symm)
  let v (n : ℕ) : F ⋙ eval ℓ T n ≅ eval ℓ S n ⋙ push ℓ d n :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (component n M)
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  exact v

private theorem eval_preservesColimits (V : Scheme.{u}) (n : ℕ) : PreservesColimitsOfSize.{u+1,u+1} (eval ℓ V n) := by
  have : PreservesColimitsOfSize.{u+1,u+1}
      (SemilinearSections.evaluation _ (rings ℓ V) (steps ℓ V) n) :=
    WeilII.ringedSequenceEvaluation_preservesColimits _ n _
  have := SheafOfModules.restrictScalars_isEquivalence_of_isIso.{u+1}
    (realizationRingIso V.smallEtaleTopology (Coeff ℓ n)).inv
  unfold eval
  infer_instance

private theorem eval_detectsIso (V : Scheme.{u}) {M N : Systems ℓ V} (f : M ⟶ N) (hf : ∀ n, IsIso ((eval ℓ V n).map f)) :
      IsIso f := by
  let H := SheafOfModules.forget (systemRing ℓ V) ⋙ PresheafOfModules.toPresheaf _
  have : IsIso (H.map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    let n := U.unop.1
    let W := op U.unop.2
    let G := sheafToPresheaf V.smallEtaleTopology (ModuleCat.{u+1} (Coeff ℓ n)) ⋙
      (CategoryTheory.evaluation _ _).obj W
    have hb := (ConcreteCategory.isIso_iff_bijective (G.map ((eval ℓ V n).map f))).1 inferInstance
    exact (evalSections ℓ V n N W).bijective.comp
      (hb.comp (evalSections ℓ V n M W).symm.bijective)
  exact isIso_of_reflects_iso f H


private theorem push_colimits
    (F : Systems ℓ S ⥤ Systems ℓ T)
    (v : EvalSquares ℓ d F) : PreservesColimitsOfSize.{u+1,u+1} F := by
  have groth (V : Scheme.{u}) : IsGrothendieckAbelian.{u+1} (Systems ℓ V) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,0}
      _ (SemilinearSections.systemRing _ (rings ℓ V) (steps ℓ V))).1
  have hcol := eval_preservesColimits ℓ
  constructor
  intro K _
  constructor
  intro A
  have : IsIso (colimit.post A F) := by
    apply eval_detectsIso ℓ T
    intro n
    let E := eval ℓ T n
    have : (push ℓ d n).IsLeftAdjoint :=
      (Etale.lowerStarClosedUpperShriekAdjunction _ d d.openComplement.ι
        d.range_eq_compl_range_openComplement_ι).isLeftAdjoint
    have : PreservesColimitsOfShape K (F ⋙ E) :=
      preservesColimitsOfShape_of_natIso (v n).symm
    have : IsIso (colimit.post (A ⋙ F) E ≫ E.map (colimit.post A F)) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (A ⋙ F) E) _
  exact preservesColimit_of_isIso_post F A

private theorem push_limits
    (F : Systems ℓ S ⥤ Systems ℓ T)
    (v : EvalSquares ℓ d F) : PreservesFiniteLimits F := by
  constructor
  intro K _ _
  constructor
  intro A
  have : IsIso (limit.post A F) := by
    apply eval_detectsIso ℓ T
    intro n
    let E := eval ℓ T n
    have : PreservesLimitsOfShape K (F ⋙ E) :=
      preservesLimitsOfShape_of_natIso (v n).symm
    have : IsIso (E.map (limit.post A F) ≫ limit.post (A ⋙ F) E) := by
      rw [limit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (limit.post (A ⋙ F) E)
  exact preservesLimit_of_isIso_post F A

private theorem derivedAdjoint_exists (F : Systems ℓ S ⥤ Systems ℓ T) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesColimitsOfSize.{u+1,u+1} F] :
    ∃ D, Nonempty (pushD ℓ F ⊣ D) := by
  have groth (V : Scheme.{u}) : IsGrothendieckAbelian.{u+1} (Systems ℓ V) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,0}
      _ (SemilinearSections.systemRing _ (rings ℓ V) (steps ℓ V))).1
  have : F.IsLeftAdjoint := isLeftAdjoint_of_preservesColimits_of_isSeparating
    (isSeparator_separator (Systems ℓ S)) F
  have adj₀ := Adjunction.ofIsLeftAdjoint F
  have : F.rightAdjoint.Additive := adj₀.right_adjoint_additive
  have : Abelian.HasKInjectiveResolutions (Systems ℓ T) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  exact ⟨F.rightAdjoint.rightDerivedFunctor, ⟨adj₀.mapDerivedCategoryRightDerivedAdjunction⟩⟩

/-- The equivalence from the ring-sheaf presentation to fixed étale coefficients. -/
abbrev fixedCoordinates (V : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.restrictScalars.{u+1} (realizationRingIso V.smallEtaleTopology (Coeff ℓ n)).inv ⋙
    V.etaleConstantModuleRestrictionFunctor (Coeff ℓ n)

private theorem fixedCoordinates_equivalence (V : Scheme.{u}) (n : ℕ) :
    (fixedCoordinates ℓ V n).IsEquivalence := by
  have := SheafOfModules.restrictScalars_isEquivalence_of_isIso.{u+1}
    (realizationRingIso V.smallEtaleTopology (Coeff ℓ n)).inv
  unfold fixedCoordinates
  infer_instance

private theorem fixedCoordinates_additive (V : Scheme.{u}) (n : ℕ) :
    (fixedCoordinates ℓ V n).Additive := ⟨by intros; ext U x; rfl⟩

/-- Evaluation in fixed module coefficients has a derived singleton left adjoint supported
at and below the input level. Both changes from the ringed-site model are equivalences. -/
theorem quotientEvaluation_singleton (V : Scheme.{u}) (n : ℕ) :
    ∃ L, Nonempty (L ⊣ ev ℓ V n) ∧
      ∀ m, n < m → ∀ P, IsZero ((ev ℓ V m).obj (L.obj P)) := by
  let J := V.smallEtaleTopology
  let level (m : ℕ) := SemilinearSections.evaluation J (rings ℓ V) (steps ℓ V) m
  let coords := fixedCoordinates ℓ V
  have (m : ℕ) : (coords m).IsEquivalence := fixedCoordinates_equivalence ℓ V m
  have (m : ℕ) : (coords m).Additive := fixedCoordinates_additive ℓ V m
  let W (m : ℕ) := (coords m).mapDerivedCategory.asEquivalence
  let w (m : ℕ) : SemilinearSections.e J (rings ℓ V) (steps ℓ V) m ⋙ (W m).functor ≅
      ev ℓ V m := Functor.mapDerivedCategoryCompIso (level m) (coords m)
  obtain ⟨L, ⟨adj⟩, hL⟩ := WeilII.semilinearSingleton_supportedAbove.{u+1, u, 0}
    J (rings ℓ V) (steps ℓ V) n
  refine ⟨(W n).inverse ⋙ L, ⟨((W n).symm.toAdjunction.comp adj).ofNatIsoRight (w n)⟩, ?_⟩
  intro m hm P
  exact ((W m).functor.map_isZero (hL m hm ((W n).inverse.obj P))).of_iso ((w m).symm.app _)

/-- Derived quotient evaluations jointly detect isomorphisms, by testing every cohomology
sheaf at every level. -/
private theorem ev_detectsIso (V : Scheme.{u}) {X Y : DS ℓ V} (f : X ⟶ Y)
    (hf : ∀ m, IsIso ((ev ℓ V m).map f)) : IsIso f := by
  apply (DerivedCategory.isIso_iff _ f).2
  intro i
  apply eval_detectsIso
  intro m
  have := hf m
  exact (NatIso.isIso_map_iff ((eval ℓ V m).mapDerivedCategoryHomologyFunctorIso i) f).2
    (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ i).map ((ev ℓ V m).map f))))

private theorem sectionwiseSquare {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Type*} [Ring R] {A B C' D E : Sheaf J (ModuleCat.{u+1} R)}
    (f : A ⟶ B) (g : B ⟶ C') (i : C' ⟶ D) (j : A ⟶ E) (k : E ⟶ D)
    (h : ∀ (U : Cᵒᵖ) (x : A.obj.obj U), i.hom.app U (g.hom.app U (f.hom.app U x)) =
      k.hom.app U (j.hom.app U x)) : f ≫ g ≫ i = j ≫ k := by
  ext U x
  exact h U x

private theorem ordinaryTransition_square
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) {a b : ℕ} (h : a ≤ b) (M : Systems ℓ S) :
    let v := systemPushEvaluations ℓ d φ
    (v b).hom.app M ≫ (push ℓ d b).map ((systemTransition ℓ S h).app M) ≫
      (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).inv.app ((eval ℓ S a).obj M) =
    (systemTransition ℓ T h).app ((systemPush ℓ d φ).obj M) ≫
      (restrict ℓ T h).map ((v a).hom.app M) := by
  apply sectionwiseSquare
  intro U x
  have he : (baseChange d).map (Prod.mkHom (homOfLE h) (𝟙 U.unop)) =
      Prod.mkHom (homOfLE h) (𝟙 (d.Etale.obj U.unop)) := by
    simp only [baseChange, Functor.prod_map, Functor.id_map, CategoryTheory.Functor.map_id]
    rfl
  exact (M.val.congr_map_apply (congrArg Quiver.Hom.op he) x).symm

set_option cleanup.letToHave false in
/-- Restricting a ring-sheaf module and reading its constant action commutes with
ordinary scalar restriction, by the identity on each group of sections. -/
def fixedRestrictionCoordinates (V : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.res (SemilinearSections.coefficientMap V.smallEtaleTopology
        (rings ℓ V) (steps ℓ V) h) ⋙ fixedCoordinates ℓ V n ≅
      fixedCoordinates ℓ V m ⋙ restrict ℓ V h := by
  let u := SemilinearSections.res (SemilinearSections.coefficientMap V.smallEtaleTopology
    (rings ℓ V) (steps ℓ V) h)
  let linearId (A B : ModuleCat.{u+1} (Coeff.{u} ℓ n)) (e : A ≃+ B) : A ≅ B :=
    LinearEquiv.toModuleIso
      { __ := e
        map_smul' := fun c x ↦ by
          obtain ⟨k, rfl⟩ := coefficient_intCast_surjective ℓ n c
          simp only [RingHom.id_apply, Int.cast_smul_eq_zsmul]
          exact map_zsmul e k x }
  let comp (M : SemilinearSections.Mod V.smallEtaleTopology (rings ℓ V m))
      (U : V.Etaleᵒᵖ) : ((u ⋙ fixedCoordinates ℓ V n).obj M).obj.obj U ≅
      ((fixedCoordinates ℓ V m ⋙ restrict ℓ V h).obj M).obj.obj U :=
    linearId _ _ (AddEquiv.refl _)
  let e (M : SemilinearSections.Mod V.smallEtaleTopology (rings ℓ V m)) :
      (u ⋙ fixedCoordinates ℓ V n).obj M ≅ (fixedCoordinates ℓ V m ⋙ restrict ℓ V h).obj M :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (comp M) (by intros; ext x; rfl))
  exact NatIso.ofComponents e (by intros; ext U x; rfl)

/-- The change-of-coefficients square acts as the identity on the underlying sections. -/
theorem fixedRestrictionCoordinates_hom_apply (V : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (B : SemilinearSections.Mod V.smallEtaleTopology (rings ℓ V m)) (U : V.Etaleᵒᵖ)
    (x : B.val.obj U) :
    (show B.val.obj U from (((fixedRestrictionCoordinates ℓ V h).hom.app B).hom.app U) x) = x := rfl

private theorem fixedCoordinates_hom_ext (V : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (A : SemilinearSections.Mod V.smallEtaleTopology (rings ℓ V n))
    (B : SemilinearSections.Mod V.smallEtaleTopology (rings ℓ V m))
    (f : A ⟶ (SemilinearSections.res (SemilinearSections.coefficientMap V.smallEtaleTopology
      (rings ℓ V) (steps ℓ V) h)).obj B)
    (g : (fixedCoordinates ℓ V n).obj A ⟶ (fixedCoordinates ℓ V m ⋙ restrict ℓ V h).obj B)
    (hg : ∀ (U : V.Etaleᵒᵖ) (x : A.val.obj U),
      (show B.val.obj U from f.val.app U x) = g.hom.app U x) :
    (fixedCoordinates ℓ V n).map f ≫ (fixedRestrictionCoordinates ℓ V h).hom.app B = g := by
  ext U x
  exact hg U x

set_option maxHeartbeats 800000 in
/-- The ordinary change from ring-sheaf coefficients to module-valued sheaves intertwines
restriction and the horizontal arrow. Source: SemilinearSystemModels.transition_exists
and EtaleConstantRingModuleEquivalence. On every test object, both composites on a module
over the lower ring have the same underlying additive group. Its identity is linear
because every upper-ring scalar lifts to an integer. These component maps and their
inverses commute with restrictions and sheaf morphisms by their identity formula. For a
system, the left composite on a section is the horizontal map by transition_exists.
The right composite has this same value by the defining hypothesis on t. Extensionality
of module morphisms on sections proves the required equality. -/
theorem ordinaryQuotientCoordinateSquare (V : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (t : eval ℓ V n ⟶ eval ℓ V m ⋙ restrict ℓ V h) (ht : IsTransition ℓ V h t) :
    let J := V.smallEtaleTopology
    let level := SemilinearSections.evaluation J (rings ℓ V) (steps ℓ V)
    let u := SemilinearSections.res (SemilinearSections.coefficientMap J (rings ℓ V) (steps ℓ V) h)
    let s : level n ⟶ level m ⋙ u := SemilinearSections.transition J (rings ℓ V) (steps ℓ V) h
    let t' : level n ⋙ fixedCoordinates ℓ V n ⟶ (level m ⋙ fixedCoordinates ℓ V m) ⋙
        restrict ℓ V h := t
    ∀ M, (fixedCoordinates ℓ V n).map (s.app M) ≫
      (fixedRestrictionCoordinates ℓ V h).hom.app ((level m).obj M) = t'.app M := by
  dsimp +zetaHave only
  intro M
  apply fixedCoordinates_hom_ext ℓ V h
  intro U x
  have raw := WeilII.semilinearTransition_section.{u+1,u,u+1} V.smallEtaleTopology
    (rings ℓ V) (steps ℓ V) h M U.unop x
  have fixed := ht M U.unop x
  exact raw.trans fixed.symm

private theorem ordinaryQuotientCoordinateSquare_exists (V : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (t : eval ℓ V n ⟶ eval ℓ V m ⋙ restrict ℓ V h) (ht : IsTransition ℓ V h t) :
    let J := V.smallEtaleTopology
    let level := SemilinearSections.evaluation J (rings ℓ V) (steps ℓ V)
    let u := SemilinearSections.res (SemilinearSections.coefficientMap J (rings ℓ V) (steps ℓ V) h)
    let s : level n ⟶ level m ⋙ u := SemilinearSections.transition J (rings ℓ V) (steps ℓ V) h
    let t' : level n ⋙ fixedCoordinates ℓ V n ⟶ (level m ⋙ fixedCoordinates ℓ V m) ⋙
        restrict ℓ V h := t
    ∃ w : u ⋙ fixedCoordinates ℓ V n ≅ fixedCoordinates ℓ V m ⋙ restrict ℓ V h,
      ∀ M, (fixedCoordinates ℓ V n).map (s.app M) ≫ w.hom.app ((level m).obj M) =
        t'.app M := by
  exact ⟨fixedRestrictionCoordinates ℓ V h, ordinaryQuotientCoordinateSquare ℓ V h t ht⟩

/-- The free singleton unit followed by an actual downward transition is universal for
restriction along the quotient. Source: SemilinearSingletonEvaluationMate, theorem
semilinearSingletonEvaluationMate_isIso, and ConstantCoefficientSystem, theorem
transition_app_apply. Identify fixed evaluation with ringed evaluation followed by
the constant-ring module equivalence. The restriction square of these equivalences is
the identity on each group of sections: a residue is an integer scalar and the ring
map fixes integer sections. The square carries the ringed transition to t by its
sectionwise formula. Localizing this square identifies the two derived transitions.
Transport the singleton adjunction by the equivalence at n and use uniqueness of the
left adjoint, with its unit. The ringed singleton theorem makes the scalar adjoint
transpose of this arrow invertible. The scalar adjunction gives the required universal
factorization, which the equivalence at m preserves and reflects. -/
theorem quotientSingleton_transition_isDerivedBaseChange (V : Scheme.{u}) {m n : ℕ}
    (h : m ≤ n) (t : eval ℓ V n ⟶ eval ℓ V m ⋙ restrict ℓ V h)
    (ht : IsTransition ℓ V h t)
    {L : Etale.DerivedCategoryModule (Coeff ℓ n) V ⥤ DS ℓ V} (a : L ⊣ ev ℓ V n)
    (P : Etale.DerivedCategoryModule (Coeff ℓ n) V) :
    Sheaf.IsDerivedBaseChange (f := quotient ℓ h)
      (a.unit.app P ≫ (transitionD ℓ V h t).app (L.obj P)) := by
  let J := V.smallEtaleTopology
  let level := SemilinearSections.evaluation J (rings ℓ V) (steps ℓ V)
  let coords := fixedCoordinates ℓ V
  let φ := SemilinearSections.coefficientMap J (rings ℓ V) (steps ℓ V) h
  let u := SemilinearSections.res φ
  let s : level n ⟶ level m ⋙ u := SemilinearSections.transition J (rings ℓ V) (steps ℓ V) h
  have (k : ℕ) : (coords k).IsEquivalence := fixedCoordinates_equivalence ℓ V k
  have (k : ℕ) : (coords k).Additive := fixedCoordinates_additive ℓ V k
  obtain ⟨w, sq⟩ := ordinaryQuotientCoordinateSquare_exists ℓ V h t ht
  obtain ⟨L₀, ⟨a₀⟩, _⟩ := WeilII.semilinearSingleton_supportedAbove.{u+1,u,0}
    J (rings ℓ V) (steps ℓ V) n
  let E (k : ℕ) := (coords k).mapDerivedCategory.asEquivalence
  exact WeilII.singletonTransition_bijective_of_equivalences (E n) (E m)
    (Functor.mapDerivedCategoryCompIso (level n) (coords n))
    (Functor.mapDerivedCategoryCompIso (level m) (coords m))
    (Functor.mapDerivedCategorySquareIso w)
    (SemilinearSections.derivedTransition J (rings ℓ V) (steps ℓ V) h) (transitionD ℓ V h t)
    (WeilII.mapDerivedCategory_transition_coordinates_square w s t sq) a₀ a P
    (WeilII.semilinearSingleton_transition_bijective.{u+1,u,0} J (rings ℓ V) (steps ℓ V) h a₀ _)

set_option cleanup.letToHave false in
/-- At every level below or equal to the input, the transpose of the closed direct-image
evaluation square is invertible on singleton extensions.
Source: SemilinearSingletonEvaluationMate (singleton units and transitions) and
CoefficientChangeLowerStar (proper direct image preserves derived base change).
In ringed coefficients the singleton unit followed by the transition represents derived
extension of scalars to level m. Transport this universal arrow across the constant-ring
equivalences, whose comparisons on sections intertwine the two quotient maps. The
direct image of the source arrow still has this universal property by proper coefficient
change. The unit identity for the transpose and the sectionwise identity of the
evaluation square identify its m-component with the comparison of these universal
arrows. The representing property supplies its inverse. -/
theorem closedDirectImageSingletonComparison_at_or_below
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) :
    let F := systemPush ℓ d φ
    let v := systemPushEvaluations ℓ d φ
    ∀ [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      ∀ {n m : ℕ}, m ≤ n →
      ∀ {Lₛ : Etale.DerivedCategoryModule (Coeff ℓ n) S ⥤ DS ℓ S}
        {Lₜ : Etale.DerivedCategoryModule (Coeff ℓ n) T ⥤ DS ℓ T}
        (aₛ : Lₛ ⊣ ev ℓ S n) (aₜ : Lₜ ⊣ ev ℓ T n) (P),
        IsIso ((ev ℓ T m).map (((mateEquiv aₛ aₜ).symm
          (Functor.mapDerivedCategorySquareIso (v n)).inv).app P)) := by
  intro F v _ _ _ n m h Lₛ Lₜ aₛ aₜ P
  let tS := systemTransition ℓ S h
  let tT := systemTransition ℓ T h
  let w := (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).symm
  have := WeilII.closedDirectImage_restrictionMate_isIso (quotient ℓ h) d
    (supportAdjunction ℓ d m) (supportAdjunction ℓ d n)
  exact WeilII.singletonEvaluationComparison_isIso aₛ aₜ
    (Functor.mapDerivedCategorySquareIso (v n)).inv
    (Functor.mapDerivedCategorySquareIso (v m)).symm
    (transitionD ℓ S h tS) (transitionD ℓ T h tT)
    (Functor.mapDerivedCategorySquareIso w).hom
    (WeilII.mapDerivedCategory_transition_square (v m) (v n) w tS tT
      (ordinaryTransition_square ℓ d φ h))
    (supportAdjunction ℓ d m) (supportAdjunction ℓ d n) P
    (quotientSingleton_transition_isDerivedBaseChange ℓ S h tS (fun _ _ _ ↦ rfl) aₛ P)
    (quotientSingleton_transition_isDerivedBaseChange ℓ T h tT (fun _ _ _ ↦ rfl) aₜ _)

set_option cleanup.letToHave false in
/-- Closed direct image commutes with free extension from one quotient level, in the
orientation determined by its sectionwise evaluation square.

Source: WeilConjectures, SystemSingletonScalarBasic, SemilinearSingletonEvaluationMate
and CoefficientChangeLowerStar. Transport the derived singleton adjunction at each site
across the two constant-ring equivalences in evaluation. Transpose the image of its
unit under closed direct image to obtain the comparison from the free extension on the
target to the pushed-forward free extension on the source. At indices above the chosen
level both evaluations vanish: a K-flat resolution of the singleton input still gives
zero there. At lower indices transpose the unit followed by the transition under derived
extension of scalars. The singleton unit theorem identifies this transpose with an
isomorphism on each site. Proper direct image preserves the resulting derived base
change arrow. The given comparison of evaluations acts identically on sections, hence
carries the horizontal maps to the actual restrictions in this calculation. Thus each
evaluation of the free-extension comparison is invertible. Exact evaluations detect
acyclic cones by reading their cohomology sheaves at every pair of a level and a site
object. The comparison itself is invertible. Taking right adjoints of the composite
adjunctions gives precisely the mate of the inverse derived evaluation square. -/
theorem closedDirectImageSingletonComparison
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) :
    let F := systemPush ℓ d φ
    let v := systemPushEvaluations ℓ d φ
    ∀ [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      ∀ n, ∃ (Lₛ : Etale.DerivedCategoryModule (Coeff ℓ n) S ⥤ DS ℓ S)
        (Lₜ : Etale.DerivedCategoryModule (Coeff ℓ n) T ⥤ DS ℓ T)
        (aₛ : Lₛ ⊣ ev ℓ S n) (aₜ : Lₜ ⊣ ev ℓ T n)
        (σ : (push ℓ d n).mapDerivedCategory ⋙ Lₜ ≅ Lₛ ⋙ pushD ℓ F),
        mateEquiv aₛ aₜ (TwoSquare.mk _ _ _ _ σ.hom) =
          (Functor.mapDerivedCategorySquareIso (v n)).inv := by
  intro F v _ _ _ n
  obtain ⟨Lₛ, ⟨aₛ⟩, hs⟩ := quotientEvaluation_singleton ℓ S n
  obtain ⟨Lₜ, ⟨aₜ⟩, ht⟩ := quotientEvaluation_singleton ℓ T n
  let α := (mateEquiv aₛ aₜ).symm (Functor.mapDerivedCategorySquareIso (v n)).inv
  have (P : Etale.DerivedCategoryModule (Coeff ℓ n) S) : IsIso (α.app P) := by
    apply ev_detectsIso
    intro m
    by_cases hm : m ≤ n
    · exact closedDirectImageSingletonComparison_at_or_below ℓ d φ hm aₛ aₜ P
    · have hlt := Nat.lt_of_not_ge hm
      apply (ht m hlt _).isIso
      apply ((push ℓ d m).mapDerivedCategory.map_isZero (hs m hlt P)).of_iso
      exact (Functor.mapDerivedCategorySquareIso (v m)).app (Lₛ.obj P)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨Lₛ, Lₜ, aₛ, aₜ, asIso α, (mateEquiv aₛ aₜ).apply_symm_apply _⟩

set_option cleanup.letToHave false in
private theorem closedSupportEvaluationMate_isIso
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) :
    let F := systemPush ℓ d φ
    let v := systemPushEvaluations ℓ d φ
    ∀ [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      ∀ {D : DS ℓ T ⥤ DS ℓ S} (adj : pushD ℓ F ⊣ D) (n : ℕ),
        IsIso (supportEvaluation ℓ d F adj n (v n)) := by
  intro F v _ _ _ D adj n
  obtain ⟨Lₛ, Lₜ, aₛ, aₜ, σ, hσ⟩ := closedDirectImageSingletonComparison ℓ d φ n
  unfold supportEvaluation
  change IsIso (mateEquiv adj (supportAdjunction ℓ d n) (Functor.mapDerivedCategorySquareIso (v n)).inv)
  rw [← hσ]
  exact CategoryTheory.Adjunction.isIso_mateEquiv_mateEquiv aₛ aₜ σ (supportAdjunction ℓ d n) adj


private theorem pushforward_additive
    [Functor.IsContinuous (baseChange d) (coefficientSequenceTopology T.smallEtaleTopology)
      (coefficientSequenceTopology S.smallEtaleTopology)]
    (φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1} _ _).obj
      (systemRing ℓ S)) :
    (SheafOfModules.pushforward.{u+1} φ).Additive :=
  ⟨by intros; ext U x; rfl⟩

/-- Read the general derived mate equation in the quotient system's fixed coefficient
coordinates. Source: the definitions of transitionD, supportEvaluation and
supportRestriction in this module, and DerivedTransitionMateEquation. Expand the
two transitions: each is the localization of the ordinary transition followed by
the inverse composition comparison. At level n the evaluation mate uses the
inverse of the localized square for v n and the two prescribed adjunctions. The
restriction mate uses the forward localization of the inverse ordinary scalar
comparison. Thus each of the three component maps in the given equation is the
corresponding component in the conclusion. Reading the composite using the
derived functor of the exact scalar restriction gives the displayed identity. -/
theorem quotientSupportTransition_coordinates (F : Systems ℓ S ⥤ Systems ℓ T)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (v : EvalSquares ℓ d F) {a b : ℕ} (h : a ≤ b)
    (tS : eval ℓ S b ⟶ eval ℓ S a ⋙ restrict ℓ S h)
    (tT : eval ℓ T b ⟶ eval ℓ T a ⋙ restrict ℓ T h)
    {D : DS ℓ T ⥤ DS ℓ S} (adj : pushD ℓ F ⊣ D) (N : DS ℓ T)
    (_h : WeilII.DerivedTransitionMateEquation (v a) (v b)
      (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).symm tS tT
      adj (supportAdjunction ℓ d a) (supportAdjunction ℓ d b) N) :
    (transitionD ℓ S h tS).app (D.obj N) ≫
      (Sheaf.derivedRestrictScalars S.smallEtaleTopology (quotient ℓ h)).map
        ((supportEvaluation ℓ d F adj a (v a)).app N) ≫
      (supportRestriction ℓ d h).app ((ev ℓ T a).obj N) =
    (supportEvaluation ℓ d F adj b (v b)).app N ≫
      (Etale.rightDerivedUpperShriek (Coeff ℓ b) d).map ((transitionD ℓ T h tT).app N) := by
  apply WeilII.TransitionComponentEquation.eq
  exact WeilII.DerivedTransitionMateEquation.components (v a) (v b) (Etale.lowerStarCompRestrictScalarsIso
    (quotient ℓ h) d).symm tS tT adj (supportAdjunction ℓ d a) (supportAdjunction ℓ d b) N _h

private theorem quotientSupportTransition_of_sectionSquare (F : Systems ℓ S ⥤ Systems ℓ T)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (v : EvalSquares ℓ d F) {a b : ℕ} (h : a ≤ b)
    (tS : eval ℓ S b ⟶ eval ℓ S a ⋙ restrict ℓ S h)
    (tT : eval ℓ T b ⟶ eval ℓ T a ⋙ restrict ℓ T h)
    (hs : ∀ M, (v b).hom.app M ≫ (push ℓ d b).map (tS.app M) ≫
      (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).inv.app ((eval ℓ S a).obj M) =
      tT.app (F.obj M) ≫ (restrict ℓ T h).map ((v a).hom.app M))
    {D : DS ℓ T ⥤ DS ℓ S} (adj : pushD ℓ F ⊣ D) (N : DS ℓ T) :
    (transitionD ℓ S h tS).app (D.obj N) ≫
      (Sheaf.derivedRestrictScalars S.smallEtaleTopology (quotient ℓ h)).map
        ((supportEvaluation ℓ d F adj a (v a)).app N) ≫
      (supportRestriction ℓ d h).app ((ev ℓ T a).obj N) =
    (supportEvaluation ℓ d F adj b (v b)).app N ≫
      (Etale.rightDerivedUpperShriek (Coeff ℓ b) d).map ((transitionD ℓ T h tT).app N) := by
  apply quotientSupportTransition_coordinates ℓ d F v h tS tT adj N
  exact WeilII.derivedTransition_mate_of_commutative_square (v a) (v b)
    (Etale.lowerStarCompRestrictScalarsIso (quotient ℓ h) d).symm tS tT hs
    adj (supportAdjunction ℓ d a) (supportAdjunction ℓ d b) N

private theorem restriction_isIso {a b : ℕ} (h : a ≤ b) : IsIso (supportRestriction ℓ d h) :=
  WeilII.closedDirectImage_restrictionMate_isIso (quotient ℓ h) d
    (supportAdjunction ℓ d a) (supportAdjunction ℓ d b)

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
/-- On the étale sequence site of the positive-power quotients, closed direct image
has a right adjoint. Its evaluations are the finite exceptional pullbacks and their
semilinear arrows are obtained by applying support and changing coefficients.

Source: Zhang, §2, closed support of the finite coefficient tower. The finite adjunction
and proper coefficient comparison are from WeilConjectures' ClosedImmersionUpperShriek
and CoefficientChangeLowerStar. The system argument uses SystemSingletonScalarBasic
and SemilinearSingletonEvaluationMate.

Covers on the sequence site are tested on the vertical slices, so level-preserving
étale base change is continuous. The sheafification units on the constant quotient
rings give its coefficient map. On a test object the resulting closed direct image
takes sections on the base-changed test object, including their original horizontal
restrictions. This gives the indicated sectionwise evaluation squares. Closed direct
image is exact at each level by the geometric stalk formula. Exactness of a sequence
of systems is detected at the levels, so this functor localizes termwise.

On ordinary systems the direct image preserves all small colimits. Indeed, every
vertical evaluation preserves them by cocontinuity of the slice inclusion, the
finite closed direct images have ordinary support right adjoints, and evaluation
jointly detects isomorphisms on sections. The special adjoint functor theorem
therefore gives a right adjoint since the source is Grothendieck abelian. Deriving
this right adjoint using K-injective resolutions gives the unbounded adjunction
with the exact direct image.

The left adjoint of evaluation freely extends a complex at a single level. Above
that level its evaluations vanish. Below it, the adjoint of the unit followed by
the horizontal transition is derived extension of scalars. The comparison from
free extension after closed direct image to closed direct image after free extension
is the transpose of direct image of the singleton unit. At each lower level it is
invertible by proper direct image preserving derived extension of finite coefficients.
Above the singleton level both sides vanish. Evaluation detects acyclicity of the
cone, so the comparison is invertible on systems. Taking its conjugate by the
composite adjunctions gives exactly the mate defining supportEvaluation.

For a quotient, the same proper coefficient comparison identifies extension of
scalars before and after closed direct image. Its conjugate is the invertible
supportRestriction. Its transpose first interchanges direct image and scalar
restriction on sections, then applies restriction to the lower-level support counit. Read each horizontal restriction
as a morphism of fixed-ring sheaves and localize it on complexes. Transpose the
displayed transition equation by the finite support adjunction at the upper level.
The two sides become the horizontal naturality square of the single system counit,
by the mate formulas for supportEvaluation and supportRestriction. This also covers
equal indices, where the section map is the identity. -/
theorem etaleQuotientSystemClosedSupportEvaluation (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (d : S ⟶ T) [IsClosedImmersion d] :
    ∃ hc : (baseChange d).IsContinuous (coefficientSequenceTopology T.smallEtaleTopology)
        (coefficientSequenceTopology S.smallEtaleTopology),
    letI := hc
    ∃ φ : systemRing ℓ T ⟶ ((baseChange d).sheafPushforwardContinuous RingCat.{u+1}
        _ _).obj (systemRing ℓ S),
      PreservesConstants ℓ d φ ∧
      let F : Systems ℓ S ⥤ Systems ℓ T := SheafOfModules.pushforward φ
      ∃ (_ : F.Additive) (_ : PreservesFiniteLimits F) (_ : PreservesFiniteColimits F)
        (v : ∀ n, F ⋙ eval ℓ T n ≅ eval ℓ S n ⋙ push ℓ d n),
        (∀ (n : ℕ) (M : Systems ℓ S) (U : T.Etale)
          (x : M.val.obj (op ((baseChange d).obj (n, U)))),
          ((v n).hom.app M).hom.app (op U) x = x) ∧
        ∃ (D : DS ℓ T ⥤ DS ℓ S) (adj : pushD ℓ F ⊣ D),
          let e := fun n ↦ supportEvaluation ℓ d F adj n (v n)
          (∀ n, IsIso (e n)) ∧
          ∀ {a b : ℕ} (h : a ≤ b),
            IsIso (supportRestriction ℓ d h) ∧
            ∃ (tS : eval ℓ S b ⟶ eval ℓ S a ⋙ restrict ℓ S h)
              (tT : eval ℓ T b ⟶ eval ℓ T a ⋙ restrict ℓ T h),
              IsTransition ℓ S h tS ∧ IsTransition ℓ T h tT ∧
              ∀ N : DS ℓ T,
                (transitionD ℓ S h tS).app (D.obj N) ≫
                    (Sheaf.derivedRestrictScalars S.smallEtaleTopology (quotient ℓ h)).map
                      ((e a).app N) ≫ (supportRestriction ℓ d h).app ((ev ℓ T a).obj N) =
                  (e b).app N ≫ (Etale.rightDerivedUpperShriek (Coeff ℓ b) d).map
                    ((transitionD ℓ T h tT).app N) := by
  classical
  obtain ⟨hc, φ, hφ⟩ := coefficientMap_exists ℓ d
  let := hc
  refine ⟨hc, φ, hφ, ?_⟩
  let F : Systems ℓ S ⥤ Systems ℓ T := SheafOfModules.pushforward φ
  have : F.Additive := pushforward_additive ℓ d φ
  let v := systemPushEvaluations ℓ d φ
  have := push_colimits ℓ d F v
  have := push_limits ℓ d F v
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  obtain ⟨D, ⟨adj⟩⟩ := derivedAdjoint_exists ℓ F
  refine ⟨‹F.Additive›, ‹PreservesFiniteLimits F›, ‹PreservesFiniteColimits F›, v, (fun _ _ _ _ ↦ rfl), D, adj, ?_⟩
  constructor
  · exact closedSupportEvaluationMate_isIso ℓ d φ adj
  · intro a b h
    let tS := systemTransition ℓ S h
    let tT := systemTransition ℓ T h
    exact ⟨restriction_isIso ℓ d h, tS, tT, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
      quotientSupportTransition_of_sectionSquare ℓ d F v h tS tT (ordinaryTransition_square ℓ d φ h) adj⟩

end WeilII.EtaleQuotientSystem
