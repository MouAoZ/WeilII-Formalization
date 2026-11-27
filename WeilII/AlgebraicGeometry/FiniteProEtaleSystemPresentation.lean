module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteCoefficientSystemEvaluation

/-!
# Simultaneous integral reduction in finite pro-étale coefficients

We use the ringed sequence site of WeilConjectures' `SemilinearSystemModels`. Its coefficient
at index `n` is the constant ring sheaf of the quotient modulo `ℓ^(n+1)`. The constant-section
isomorphisms of `FiniteCoefficientSystemEvaluation` identify this ring tower with the one used
by `CoherentReduction.reductionBc`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProEtale.CoherentReduction
open WeilConjectures.SemilinearSections

namespace WeilII.FiniteProEtaleSystem

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u})

/-- The positive-power quotient in the universe used by `CoherentReduction.reductionBc`. -/
abbrev Coeff (n : ℕ) := Etale.FiniteProperQuotient.Ring ℓ (ULift.{u + 1} ℚ_[ℓ]) n

/-- The constant sheaf of finite coefficients at index `n`, as in `finiteConstantIso`. -/
abbrev rings (n : ℕ) := realizationRing (Scheme.ProEt.topology V) (Coeff.{u} ℓ n)

/-- Sheafify the actual adjacent residue homomorphism of `Etale.FiniteProperQuotient`. -/
def steps (n : ℕ) : rings ℓ V (n + 1) ⟶ rings ℓ V n :=
  (constantSheaf (Scheme.ProEt.topology V) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient ℓ (ULift.{u + 1} ℚ_[ℓ]) n.le_succ))

/-- The derived category of strict systems on the constant finite ring tower,
in the sequence-site model of `SemilinearSystemModels`. -/
abbrev Derived := DS.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (rings ℓ V) (steps ℓ V)

/-- Adjacent quotient maps commute with the constant-section maps, by
`finiteConstantIso_hom_coefficientMap` at `n ≤ n+1`. -/
theorem constantSections_step (n : ℕ) :
    (finiteConstantIso V (Coeff.{u} ℓ (n + 1))).hom ≫ transitions ℓ (ULift.{u + 1} ℚ_[ℓ]) V n =
      steps ℓ V n ≫ (finiteConstantIso V (Coeff.{u} ℓ n)).hom := by
  simpa only [steps, Coeff, WeilConjectures.SemilinearSections.coefficientMap,
    WeilConjectures.SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ] using
    finiteConstantIso_hom_coefficientMap ℓ (ULift.{u + 1} ℚ_[ℓ]) V n.le_succ

/-- The constant-section isomorphism on the whole sequence site. Its component at `(n, U)`
is the component of `finiteConstantIso` at `U`, by `systemMap_existsUnique`. -/
def constantSectionsIso :
    systemRing (Scheme.ProEt.topology V) (rings ℓ V) (steps ℓ V) ≅
      systemRing (Scheme.ProEt.topology V) (coefficients ℓ (ULift.{u + 1} ℚ_[ℓ]) V)
        (transitions ℓ (ULift.{u + 1} ℚ_[ℓ]) V) := by
  let spec := systemMap_existsUnique (Scheme.ProEt.topology V) (rings ℓ V) (steps ℓ V)
    (coefficients ℓ (ULift.{u + 1} ℚ_[ℓ]) V) (transitions ℓ (ULift.{u + 1} ℚ_[ℓ]) V)
    (fun n ↦ (finiteConstantIso V (Coeff.{u} ℓ n)).hom) (constantSections_step ℓ V)
  let f := spec.exists.choose
  have h (W : (ℕ × V.ProEt)ᵒᵖ) : IsIso (f.hom.app W) := by
    rw [show f.hom.app W = _ from spec.exists.choose_spec W.unop.1 (op W.unop.2)]
    exact (((sheafToPresheaf _ _).mapIso (finiteConstantIso V (Coeff.{u} ℓ W.unop.1))).app
      (op W.unop.2)).isIso_hom
  have : IsIso ((sheafToPresheaf _ _).map f) := NatIso.isIso_of_isIso_app f.hom
  have : IsIso f := isIso_of_reflects_iso f (sheafToPresheaf _ _)
  exact asIso f

/-- Evaluation in sheaves of modules over the fixed finite ring. After evaluation on the
sequence site, read the action on the same additive sheaf by restriction to constant sections,
as in `CoherentReduction.finiteUnrealization`. -/
def evaluation (n : ℕ) :
    Derived ℓ V ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (Coeff ℓ n))) := by
  let J := Scheme.ProEt.topology V
  let A := Coeff.{u} ℓ n
  letI := ConstantScalarRestriction.additive J A
  letI := (ConstantScalarRestriction.exact J A).1
  letI := (ConstantScalarRestriction.exact J A).2
  exact e J (rings ℓ V) (steps ℓ V) n ⋙
    (ConstantScalarRestriction.restriction J A).mapDerivedCategory

/-- At each vertex the sequence-site presentation gives the fixed-module evaluation of
`FiniteCoefficientSystemEvaluation`. The restriction/evaluation comparison is induced by the
identity on additive sections, followed by the same constant scalar action on both sides. -/
def evaluationIso (n : ℕ) :
    resD (constantSectionsIso ℓ V).hom ⋙ evaluation ℓ V n ≅
      fixedDerivedEvaluation ℓ (ULift.{u + 1} ℚ_[ℓ]) V n := by
  let J := Scheme.ProEt.topology V
  let E := ULift.{u + 1} ℚ_[ℓ]
  let A := Coeff.{u} ℓ n
  let H : WeilConjectures.SemilinearSections.Mod J (rings ℓ V n) ⥤
      Sheaf J (ModuleCat.{u + 1} A) := ConstantScalarRestriction.restriction J A
  letI : H.Additive := ConstantScalarRestriction.additive J A
  letI : Limits.PreservesFiniteLimits H := (ConstantScalarRestriction.exact J A).1
  letI : Limits.PreservesFiniteColimits H := (ConstantScalarRestriction.exact J A).2
  let δ := restrictionEvaluation J (rings ℓ V) (steps ℓ V) (coefficients ℓ E V)
    (transitions ℓ E V) (fun i ↦ (finiteConstantIso V (Coeff.{u} ℓ i)).hom) (constantSections_step ℓ V) n
  exact Functor.isoWhiskerRight δ H.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (e J (coefficients ℓ E V) (transitions ℓ E V) n)
      (Functor.mapDerivedCategoryCompIso
        (C₂ := WeilConjectures.SemilinearSections.Mod J (rings ℓ V n))
        (res (finiteConstantIso V A).hom) H)

end WeilII.FiniteProEtaleSystem

namespace WeilII

universe u

/-- Simultaneous reduction of a bounded constructible integral complex in the finite
pro-étale system. Apply `CoherentReduction.reductionBc` for the lifted ℓ-adic field, then
restrict scalars on the sequence site along its constant-section isomorphism. Restriction is
exact and preserves the underlying horizontal maps. At level `n`,
`FiniteProEtaleSystem.evaluation` reads the resulting action over the quotient modulo `ℓ^(n+1)`.
Sources: WeilConjectures, `CoherentIntegralReduction` and `FiniteCoefficientSystemEvaluation`. -/
def finiteProEtaleSystemPresentation (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u}) :
    Bc ℓ (ULift.{u + 1} ℚ_[ℓ]) V ⥤ FiniteProEtaleSystem.Derived ℓ V :=
  reductionBc ℓ (ULift.{u + 1} ℚ_[ℓ]) V ⋙ resD (FiniteProEtaleSystem.constantSectionsIso ℓ V).hom

end WeilII
