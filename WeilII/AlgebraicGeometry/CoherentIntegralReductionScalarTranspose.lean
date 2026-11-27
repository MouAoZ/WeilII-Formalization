module

public import WeilII.AlgebraicGeometry.CoherentIntegralReductionEvaluation
public import WeilII.AlgebraicGeometry.FiniteProEtaleTowerGeometry
public import WeilII.AlgebraicGeometry.FiniteProEtaleEvaluationDetectsIso
public import WeilConjectures.WeilSheaf.SmoothPuritySemilinearReading
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsSquare

/-! # Transposing the integral scalar unit on the entire sequence site -/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CoherentReduction WeilConjectures.SemilinearSections
open WeilII.FiniteProEtaleTowerGeometry

namespace WeilII.CoherentReductionTranspose

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (ℓ : ℕ) [Fact ℓ.Prime]

abbrev integral (V : Scheme.{u}) :=
  sectionRing V (Padic.coefficientExtensionIntegers ℓ (ULift.{u+1} ℚ_[ℓ]))

abbrev intSystem (V : Scheme.{u}) :=
  DS.{u+1,u,u+1} (Scheme.ProEt.topology V)
    (constantCoefficients.{u+1,u,u+1} (Scheme.ProEt.topology V) (integral ℓ V))
    (constantCoefficientTransitions.{u+1,u,u+1} (Scheme.ProEt.topology V) (integral ℓ V))

/-- The integral input before simultaneous scalar extension, including the diagonal. -/
abbrev input (V : Scheme.{u}) :=
  CoherentIntegralEvaluation.integralTransport ℓ V ⋙ (boundedConstructible _).ι ⋙
    (integralSections ℓ (ULift.{u+1} ℚ_[ℓ]) V).mapDerivedCategory ⋙
    derivedConstantSystem.{u+1,u,u+1} (Scheme.ProEt.topology V) (integral ℓ V)

/-- The exact change from quotient section rings to constant quotient rings. -/
abbrev readSystem (V : Scheme.{u}) := resD (FiniteProEtaleSystem.constantSectionsIso ℓ V).hom

/-- Transport along the sequence-ring isomorphism uses restriction in both directions.
The cancellation maps are the identity on additive sections. -/
def readingEquivalence (V : Scheme.{u}) :=
  let i := FiniteProEtaleSystem.constantSectionsIso ℓ V
  let j := (sheafCompose (site V) (forget₂ CommRingCat.{u+1} RingCat)).mapIso i
  CategoryTheory.Equivalence.mk (res.{u+1,u,u+1} i.hom) (res.{u+1,u,u+1} i.inv)
    (SheafOfModules.restrictScalarsCancelIso j.inv j.hom j.inv_hom_id).symm
    (SheafOfModules.restrictScalarsCancelIso j.hom j.inv j.hom_inv_id)

/-- The scalar adjunction with the finite side in fixed sequence coefficients. -/
abbrev scalarAdj (V : Scheme.{u}) :=
  let i := FiniteProEtaleSystem.constantSectionsIso ℓ V
  let E := readingEquivalence ℓ V
  let H := res.{u+1,u,u+1} i.hom
  let G := res.{u+1,u,u+1} i.inv
  let u : 𝟭 _ ≅ H ⋙ G := E.unitIso
  let c : G ⋙ H ≅ 𝟭 _ := E.counitIso
  let D := CategoryTheory.Equivalence.mk H.mapDerivedCategory G.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso _).symm ≪≫ Functor.mapDerivedCategoryNatIso u ≪≫
      (Functor.mapDerivedCategoryCompIso H G).symm)
    (Functor.mapDerivedCategoryCompIso G H ≪≫ Functor.mapDerivedCategoryNatIso c ≪≫
      Functor.mapDerivedCategoryIdIso _)
  (reductionScalar ℓ (ULift.{u+1} ℚ_[ℓ]) V).scalar.adjunction.comp D.toAdjunction

abbrev extend (V : Scheme.{u}) :=
  (reductionScalar ℓ (ULift.{u+1} ℚ_[ℓ]) V).scalar.T ⋙ readSystem ℓ V

abbrev restrict (V : Scheme.{u}) := resD (FiniteProEtaleSystem.constantSectionsIso ℓ V).inv ⋙
  resD (systemMap (Scheme.ProEt.topology V) _ _ _ _
    (CoherentReduction.coefficientMap ℓ (ULift.{u+1} ℚ_[ℓ]) V)
    (coefficientMap_compatible ℓ (ULift.{u+1} ℚ_[ℓ]) V))

abbrev present (V : Scheme.{u}) :=
  CoherentIntegralEvaluation.integralTransport ℓ V ⋙ finiteProEtaleSystemPresentation ℓ V

abbrev integralPull {S T : Scheme.{u}} (f : S ⟶ T) :=
  CondensedRing.purityBoundedConstructiblePullback (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) f

local instance {S T : Scheme.{u}} (f : S ⟶ T) : (pull ℓ f).Additive := (pull_exact ℓ f).1
local instance {S T : Scheme.{u}} (f : S ⟶ T) : PreservesFiniteLimits (pull ℓ f) :=
  (pull_exact ℓ f).2.1
local instance {S T : Scheme.{u}} (f : S ⟶ T) : PreservesFiniteColimits (pull ℓ f) :=
  (pull_exact ℓ f).2.2

abbrev finitePull {S T : Scheme.{u}} (f : S ⟶ T) := (pull ℓ f).mapDerivedCategory

/-- The two squares used in transposing the scalar unit. The integral diagonal and
restriction comparisons live on the whole system, including its horizontal arrows. -/
structure Squares {S T : Scheme.{u}} (f : S ⟶ T) where
  integralSystemPull : intSystem ℓ T ⥤ intSystem ℓ S
  diagonal : integralPull ℓ f ⋙ input ℓ S ≅ input ℓ T ⋙ integralSystemPull
  restriction : restrict ℓ T ⋙ integralSystemPull ≅ finitePull ℓ f ⋙ restrict ℓ S

/-- Apply integral-system pullback to the target unit, rewrite restriction by its
comparison, and transpose at the source. This produces one morphism of whole systems. -/
def forward {S T : Scheme.{u}} {f : S ⟶ T} (s : Squares ℓ f) :
    integralPull ℓ f ⋙ present ℓ S ⟶ present ℓ T ⋙ finitePull ℓ f := by
  let g : integralPull ℓ f ⋙ input ℓ S ⟶ (present ℓ T ⋙ finitePull ℓ f) ⋙ restrict ℓ S :=
    s.diagonal.hom ≫ Functor.whiskerLeft (input ℓ T)
      (Functor.whiskerRight (scalarAdj ℓ T).unit s.integralSystemPull ≫
        Functor.whiskerLeft (extend ℓ T) s.restriction.hom)
  exact (((scalarAdj ℓ S).whiskerRight _).homEquiv _ _).symm g

/-- Joint detection by fixed finite evaluations inverts the transpose on the whole
derived category. The criterion applies to every scheme. -/
def comparison {S T : Scheme.{u}} {f : S ⟶ T} (s : Squares ℓ f)
    (h : ∀ K n, IsIso ((FiniteProEtaleSystem.evaluation ℓ S n).map ((forward ℓ s).app K))) :
    present ℓ T ⋙ finitePull ℓ f ≅ integralPull ℓ f ⋙ present ℓ S := by
  have : IsIso (forward ℓ s) := (NatTrans.isIso_iff_isIso_app _).2 fun K ↦
    FiniteProEtaleSystem.evaluation_detects_iso ℓ S _ (h K)
  exact (asIso (forward ℓ s)).symm

end WeilII.CoherentReductionTranspose
