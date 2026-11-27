module

public import WeilII.AlgebraicGeometry.FiniteProEtaleSystemPresentation
public import WeilII.AlgebraicGeometry.CoherentIntegralQuotientComparison
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived

/-!
# Evaluation of coherent integral reduction

For the integral coefficients used before (†) on page 2 of Zhang, we compare the sequence-site
scalar adjunction of `CoherentReduction` with the internal-module adjunction of
`IntegralReductionConstructible`. The coefficient isomorphisms come from
`exists_coherentIntegralQuotientComparison`. Index `n` represents the quotient modulo `ℓ^(n+1)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CoherentReduction WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace WeilII.CoherentIntegralEvaluation

universe u w

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u})

local notation "J" => Scheme.ProEt.topology V
local notation "A" => PadicAlgCl.integers ℓ ℚ_[ℓ]
local notation "B" => PadicAlgCl.integersModPow ℓ ℚ_[ℓ]

/-- The small integral coefficient uses the subspace topology from the norm on ℚℓ in
`exists_coherentIntegralQuotientComparison`. -/
local instance : TopologicalSpace A := TopologicalSpace.induced Subtype.val
  (PadicAlgCl.normedFieldOfAlgebra ℓ ℚ_[ℓ]).toUniformSpace.toTopologicalSpace

/-- The ring operations are continuous for this topology by
`PadicAlgCl.isTopologicalRing_integers`. -/
local instance : IsTopologicalRing A := PadicAlgCl.isTopologicalRing_integers ℓ ℚ_[ℓ]

/-- The residue-ring isomorphism of `exists_coherentIntegralQuotientComparison` sends the
class of an integral representative to the class of its universe lift. -/
abbrev residueEquiv (n : ℕ) : ULift.{u + 1} (B (n + 1)) ≃+* FiniteProEtaleSystem.Coeff.{u} ℓ n :=
  (exists_coherentIntegralQuotientComparison ℓ V).choose_spec.choose_spec.2.2.choose n

/-- The integral isomorphism on the scheme obtained by pulling back the continuous
coefficient comparison from the point, as in `exists_coherentIntegralQuotientComparison`. -/
def integralIso :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V ≅
      internalRing V (Padic.coefficientExtensionIntegers ℓ (ULift.{u + 1} ℚ_[ℓ])) := by
  let h := exists_coherentIntegralQuotientComparison ℓ V
  let a := (upperStarFromPoint V).map ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab)).map
    (coherentCoefficientPointMap h.choose.toRingHom h.choose_spec.choose))
  letI : IsIso a := h.choose_spec.choose_spec.2.2.choose_spec.2.2.1
  exact asIso a

/-- The corresponding isomorphism of finite coefficient objects, induced by `residueEquiv`. -/
def residueIso (n : ℕ) :
    condensedRingObj (Profinite.integersModPowRingObj ℓ ℚ_[ℓ] (n + 1)) V ≅
      internalRing V (FiniteProEtaleSystem.Coeff.{u} ℓ n) := by
  let h := exists_coherentIntegralQuotientComparison ℓ V
  let f := (residueEquiv ℓ V n).toRingHom.comp ULift.ringEquiv.symm.toRingHom
  let b := (upperStarFromPoint V).map ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab)).map
    (coherentCoefficientPointMap f continuous_of_discreteTopology))
  letI : IsIso b := (h.choose_spec.choose_spec.2.2.choose_spec.2.2.2 n).1
  exact asIso b

/-- Pullback of the integral map of sheaves of rings preserves the unit and multiplication. -/
instance : IsMonHom (integralIso ℓ V).hom := by
  dsimp only [integralIso, asIso]
  infer_instance

/-- Pullback of the residue map of sheaves of rings preserves the unit and multiplication. -/
instance (n : ℕ) : IsMonHom (residueIso ℓ V n).hom := by
  dsimp only [residueIso, asIso]
  infer_instance

/-- Transport a bounded constructible complex into the coherent coefficient universe by
exact restriction along the inverse integral ring isomorphism, using
`boundedConstructible_comap_iso_iff`. -/
def integralTransport :
    BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V) ⥤
      Bc ℓ (ULift.{u + 1} ℚ_[ℓ]) V :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
    (CategoryTheory.Mod.comap (integralIso ℓ V).inv).mapDerivedCategory)
    fun K ↦ (boundedConstructible_comap_iso_iff (integralIso ℓ V).inv K.obj).2 K.property

/-- Write a small integral module as a module over the coherent section rings,
using the section-action equivalence of `CoherentReduction.integralSections`. -/
abbrev integralEncoding :=
  CategoryTheory.Mod.comap (integralIso ℓ V).inv ⋙ integralSections ℓ (ULift.{u + 1} ℚ_[ℓ]) V

/-- Write a small quotient module as a module over the coherent section rings,
using the same internal-module/section-module equivalence at the finite ring. -/
abbrev residueEncoding (n : ℕ) :=
  CategoryTheory.Mod.comap (residueIso ℓ V n).inv ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J
      (internalRing V (FiniteProEtaleSystem.Coeff.{u} ℓ n))).functor

/-- Localize an equality with the identity functor, using the canonical
`Functor.mapDerivedCategoryIdIso` after transport. -/
def derivedIdOfEq {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{w} C]
    (F : C ⥤ C) (h : F = 𝟭 C) :
    letI : F.Additive := h.symm ▸ inferInstanceAs (𝟭 C).Additive
    letI : PreservesFiniteLimits F := h.symm ▸ inferInstanceAs (PreservesFiniteLimits (𝟭 C))
    letI : PreservesFiniteColimits F := h.symm ▸ inferInstanceAs (PreservesFiniteColimits (𝟭 C))
    F.mapDerivedCategory ≅ 𝟭 _ := by
  subst F
  exact Functor.mapDerivedCategoryIdIso C

/-- Evaluate the exact diagonal. The ordinary functors agree on objects and morphisms by
`constantSystem_existsUnique`; localize this equality termwise. -/
def diagonalEvaluation (n : ℕ) :
    let R := sectionRing V (Padic.coefficientExtensionIntegers ℓ (ULift.{u + 1} ℚ_[ℓ]))
    derivedConstantSystem.{u + 1, u, u + 1} J R ⋙
      e.{u + 1, u, u + 1} J (constantCoefficients.{u + 1, u, u + 1} J R)
        (constantCoefficientTransitions.{u + 1, u, u + 1} J R) n ≅ 𝟭 _ := by
  intro R
  let Δ := constantSystem.{u + 1, u, u + 1} J R
  let ev := WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} J
    (constantCoefficients.{u + 1, u, u + 1} J R)
    (constantCoefficientTransitions.{u + 1, u, u + 1} J R) n
  let spec := (constantSystem_existsUnique.{u + 1, u, u + 1} J R).1.exists.choose_spec
  have h : Δ ⋙ ev = 𝟭 _ := Functor.hext (fun M ↦ spec.1 M n) (fun _ _ f ↦ spec.2.1 f n)
  letI := hasDerived.{u + 1, u, u + 1} J R
  exact Functor.mapDerivedCategoryCompIso Δ ev ≪≫
    derivedIdOfEq (C := WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R) (Δ ⋙ ev) h

/-- The finite encoding preserves addition because its factors preserve binary products. -/
local instance (n : ℕ) : (residueEncoding ℓ V n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The system part of the comparison at one bounded integral complex. Apply the evaluation
of the fixed presentation, then `ScalarSystems.evaluation`, and finally evaluate the diagonal.
The last composition isomorphism incorporates the integral change of universe into the encoding. -/
def sectionEvaluation (n : ℕ)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V)) :
    (FiniteProEtaleSystem.evaluation ℓ V n).obj
        ((finiteProEtaleSystemPresentation ℓ V).obj ((integralTransport ℓ V).obj K)) ≅
      (finiteUnrealization V (FiniteProEtaleSystem.Coeff.{u} ℓ n)).mapDerivedCategory.obj
        (((reductionScalar ℓ (ULift.{u + 1} ℚ_[ℓ]) V).levels n).T.obj
          ((integralEncoding ℓ V).mapDerivedCategory.obj K.obj)) := by
  let E := ULift.{u + 1} ℚ_[ℓ]
  let H := (finiteUnrealization V (FiniteProEtaleSystem.Coeff.{u} ℓ n)).mapDerivedCategory
  let S := reductionScalar ℓ E V
  let M := (integralTransport ℓ V).obj K
  let Z := (integralSections ℓ E V).mapDerivedCategory.obj M.obj
  let Δ := derivedConstantSystem.{u + 1, u, u + 1} J
    (sectionRing V (Padic.coefficientExtensionIntegers ℓ E))
  let c := Functor.mapDerivedCategoryCompIso (CategoryTheory.Mod.comap (integralIso ℓ V).inv)
    (integralSections ℓ E V)
  exact (FiniteProEtaleSystem.evaluationIso ℓ V n).app ((reductionBc ℓ E V).obj M) ≪≫
    H.mapIso ((S.evaluation n).app (Δ.obj Z) ≪≫
      (S.levels n).T.mapIso ((diagonalEvaluation ℓ V n).app Z ≪≫ c.app K.obj))

set_option cleanup.letToHave false in
set_option maxHeartbeats 1200000 in
/-- Evaluation of simultaneous integral reduction agrees naturally with bounded internal
reduction followed by inclusion and the finite coefficient equivalence. Its component is fixed
by the scalar adjunctions and by the identity on additive sections of both ordinary comparisons.

Proof. Transport the internal modules along the two coefficient isomorphisms. The reduction
square of `exists_coherentIntegralQuotientComparison` makes the two restrictions of scalars agree
on each test object. Applying `CondensedRing.sectionModuleComapIso` gives the first ordinary
comparison ρ with component x ↦ x. At the finite end, the constant-section square of the same
coefficient comparison identifies each constant scalar in the two actions. By
`finiteCoefficientModEquivalence_smul` these actions agree, so the identity on the underlying
additive sheaf is a linear natural isomorphism σ. Localize both isomorphisms termwise.

For an integral complex X, the nth leg of `canonicalReductionTowerCone` is the internal
adjunction unit by `canonicalReductionTowerCone_π_app`. Postcompose with the restriction of
the inverse bounded inclusion comparison, encode the result, and compose with the derived ρ.
Transpose through the level scalar adjunction to obtain κ. Its naturality follows from
naturality of the unit, of ρ and of transposition. Precomposition with
κ induces on maps into every encoded finite complex the composite of the Hom bijections of the
two encoding equivalences, the two scalar adjunctions and ρ. The finite encoding is essentially
surjective, so Yoneda makes κ invertible. For the system comparison `sectionEvaluation`,
`ScalarSystems.transpose_evaluation` at the identity identifies the evaluated system unit with
the level unit. Compose the evaluated system comparison with the finite reading of κ and
the derived σ. Their naturality gives θ with the displayed components.

Sources include Zhang, p. 2 before (†), and WeilConjectures' `CoherentIntegralReduction`,
`SemilinearDerivedCalculus`, `FiniteCoefficientSystemEvaluation`,
`ContinuousCoefficientModuleEncoding` and `IntegralReductionConstructible`. -/
theorem exists_evaluationIso [TopologicalSpace.NoetherianSpace V] (n : ℕ) :
    let E := ULift.{u + 1} ℚ_[ℓ]
    let q := integersModPowReduction V ℓ ℚ_[ℓ] (n + 1)
    let r := CoherentReduction.coefficientMap ℓ E V n
    let EA := integralEncoding ℓ V
    let EB := residueEncoding ℓ V n
    let H := finiteUnrealization V (FiniteProEtaleSystem.Coeff.{u} ℓ n)
    let G := Sheaf.restrictScalars J (residueEquiv ℓ V n).toRingHom
    let Φ := finiteCoefficientDerivedEquivalence V (B (n + 1))
    let red := boundedConstructibleIntegersModPowReduction V ℓ ℚ_[ℓ] (n + 1)
    ∃ θ : integralTransport ℓ V ⋙ finiteProEtaleSystemPresentation ℓ V ⋙
          FiniteProEtaleSystem.evaluation ℓ V n ⋙ G.mapDerivedCategory ≅
        red ⋙ (boundedConstructible _).ι ⋙ Φ.functor,
      ∃ (ρ : CategoryTheory.Mod.comap q ⋙ EA ≅ EB ⋙ res.{u + 1, u, u + 1} r)
        (σ : (EB ⋙ H) ⋙ G ≅ (finiteCoefficientModEquivalence V (B (n + 1))).functor),
        (∀ M U x, (ρ.hom.app M).val.app U x = x) ∧
        (∀ M U x, (σ.hom.app M).hom.app U x = x) ∧
        let ρD := Functor.mapDerivedCategoryCompIso (CategoryTheory.Mod.comap q) EA ≪≫
          Functor.mapDerivedCategoryNatIso ρ ≪≫ (Functor.mapDerivedCategoryCompIso EB (res r)).symm
        let σD := Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso EB H)
            G.mapDerivedCategory ≪≫ Functor.mapDerivedCategoryCompIso (EB ⋙ H) G ≪≫
          Functor.mapDerivedCategoryNatIso σ
        let level := (reductionScalar ℓ E V).levels n
        ∀ K : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V),
          let X := K.obj
          let Y := (red.obj K).obj
          let ι :=
            (boundedConstructibleIntegersModPowReductionCompatibility V ℓ ℚ_[ℓ] (n + 1)).inv.app K
          let η : X ⟶ (CategoryTheory.Mod.comap q).mapDerivedCategory.obj Y :=
            (canonicalReductionTowerCone ℚ_[ℓ] X).π.app (Opposite.op n) ≫
              (CategoryTheory.Mod.comap q).mapDerivedCategory.map ι
          let κ := (level.adjunction.homEquiv _ (EB.mapDerivedCategory.obj Y)).symm
            (EA.mapDerivedCategory.map η ≫ ρD.hom.app Y)
          θ.hom.app K =
            G.mapDerivedCategory.map ((sectionEvaluation ℓ V n K).hom ≫ H.mapDerivedCategory.map κ) ≫
              σD.hom.app Y := by
  classical
  intro E q r EA EB H G Φ red
  let S := FiniteProEtaleSystem.Coeff.{u} ℓ n
  let R := ULift.{u + 1} (B (n + 1))
  let d := residueEquiv ℓ V n
  let a := integralIso ℓ V
  let smallResidue := condensedRingObj (Profinite.integersModPowRingObj ℓ ℚ_[ℓ] (n + 1)) V
  let b : smallResidue ≅ internalRing V S := residueIso ℓ V n
  let pull := upperStarFromPoint V
  let F₁ := sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat.{u + 1} RingCat)
  let F₂ := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab)
  let p := pull.map (F₂.map (F₁.map
    (continuousPointMap (quotient ℓ E n) (quotient_continuous ℓ E n))))
  -- Transport the reduction square to the inverses used by the encodings.
  let f : _ ⟶ smallResidue := constRingSheafToCondensedRingObj V (B (n + 1))
  let φ := AddCommGrpCat.ofHom d.toRingHom.toAddMonoidHom
  have squares : q ≫ b.hom = a.hom ≫ p ∧
      f ≫ b.hom = (constantSheaf J Ab.{u + 1}).map φ ≫ schemeConstants V S := by
    let spec := (exists_coherentIntegralQuotientComparison ℓ V).choose_spec.choose_spec.2.2
    have atLevel := spec.choose_spec.2.2.2 n
    exact ⟨atLevel.2.1, atLevel.2.2.2.2.2⟩
  have sq' : a.inv ≫ q = p ≫ b.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, squares.1, Iso.inv_hom_id_assoc]
  let t := (CategoryTheory.Mod.comapComp a.inv q).symm ≪≫
    CategoryTheory.Mod.comapCongr sq' ≪≫ CategoryTheory.Mod.comapComp p b.inv
  let ρ : CategoryTheory.Mod.comap q ⋙ EA ≅ EB ⋙ res.{u + 1, u, u + 1} r :=
    Functor.isoWhiskerRight t (integralSections ℓ E V) ≪≫
      Functor.isoWhiskerLeft (CategoryTheory.Mod.comap b.inv)
        (CondensedRing.sectionModuleComapIso V p)
  have hρ : ∀ M U x, (ρ.hom.app M).val.app U x = x := fun _ _ _ ↦ rfl
  let P := (EB ⋙ H) ⋙ G
  let Q := (finiteCoefficientModEquivalence V (B (n + 1))).functor
  -- Compare a constant scalar before and after the two changes of coefficient rings.
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let j := ((constantCommuteCompose J F).app (CommRingCat.of S)).inv
  let s (U : V.ProEtᵒᵖ) (c : R) :=
    (toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of S))).app U (d c)
  let v (U : V.ProEtᵒᵖ) (c : R) : (internalRing V S).obj.obj U :=
    (finiteConstantIso V S).hom.hom.app U (j.hom.app U (s U c))
  let z (U : V.ProEtᵒᵖ) (c : R) :=
    (toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (AddCommGrpCat.of R))).app U c
  have scalar (U : V.ProEtᵒᵖ) (c : R) : b.inv.hom.app U (v U c) = f.hom.app U (z U c) := by
    have hj : toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of S)) ≫ j.hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of S))) F := by
      change _ ≫ (sheafifyMap J (Functor.constComp V.ProEtᵒᵖ (CommRingCat.of S) F).inv ≫
        (sheafifyComposeIso J F _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, sheafComposeIso_hom_fac]
      ext U x
      rfl
    have hv : j.hom.app U (s U c) =
        (toSheafify J ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of S))).app U (d c) :=
      ConcreteCategory.congr_hom (congr_app hj U) (d c)
    have hmap : (finiteConstantIso V S).hom = constantSectionsRingMap V S := by
      apply (constantSections_existsUnique V S).unique
      · exact (constantSections_existsUnique V S).exists.choose_spec
      · apply heq_of_eq
        set_option backward.isDefEq.respectTransparency false in
        rw [← constantSectionsRingMap_forget, Iso.hom_inv_id_assoc]
    have hv' : v U c = (schemeConstantsPresheaf V S).app U (d c) := by
      dsimp only [v]
      rw [hv, hmap, constantSectionsRingMap_toSheafify]
    have hn := ConcreteCategory.congr_hom (congr_app
      (toSheafify_naturality J ((Functor.const V.ProEtᵒᵖ).map φ)) U) c
    let forgetAb := sheafToPresheaf J Ab.{u + 1}
    have he := ConcreteCategory.congr_hom (congr_app (congrArg forgetAb.map squares.2) U) (z U c)
    have hz : b.hom.hom.app U (f.hom.app U (z U c)) = v U c := by
      rw [hv']
      exact he.trans (congrArg ((schemeConstants V S).hom.app U) hn.symm)
    rw [← hz]
    exact ConcreteCategory.congr_hom (congr_app (congrArg forgetAb.map b.hom_inv_id) U) _
  let T :=
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J smallResidue).functor
  have lin (M : CategoryTheory.Mod (Sheaf J Ab.{u + 1}) smallResidue)
      (U : V.ProEtᵒᵖ) (c : R) (x : M.X.obj.obj U) :
      c • (show (P.obj M).obj.obj U from x) = c • (show (Q.obj M).obj.obj U from x) := by
    have h₁ := (((CondensedRing.sectionModuleComapIso V b.inv).hom.app M).val.app U).hom.map_smul
      (v U c) x
    have h₂ := (((CondensedRing.sectionModuleComapIso V f).hom.app M).val.app U).hom.map_smul
      (z U c) x
    exact h₁.trans
      ((congrArg (fun t ↦ (((T.obj M).val.obj U).smul t).asHom x) (scalar U c)).trans h₂.symm)
  let σ : P ≅ Q := NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf J _).preimageIso (NatIso.ofComponents (fun U ↦
      ModuleCat.isoMk (Iso.refl _) (fun c ↦
        ConcreteCategory.hom_ext _ _ (fun x ↦ (lin M U c x).symm)))
      (fun _ ↦ by ext; rfl))) (fun _ ↦ by ext; rfl)
  have hσ : ∀ M U x, (σ.hom.app M).hom.app U x = x := fun _ _ _ ↦ rfl
  -- Derive the ordinary comparisons and take the inverse mate between the scalar adjunctions.
  let ρD := Functor.mapDerivedCategorySquareIso (F₁ := CategoryTheory.Mod.comap q) (F₂ := EA)
    (G₁ := EB) (G₂ := res r) ρ
  let σD := Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso EB H) G.mapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso (EB ⋙ H) G ≪≫ Functor.mapDerivedCategoryNatIso σ
  let sys := reductionScalar ℓ E V
  let level := sys.levels n
  let : BraidedCategory (Sheaf J Ab.{u + 1}) := (Sheaf.symmetricCategory J _).toBraidedCategory
  have : IsCommMonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V) :=
    isCommMonObj_condensedRingObj _ V
  have : IsCommMonObj (condensedRingObj (Profinite.integersModPowRingObj ℓ ℚ_[ℓ] (n + 1)) V) :=
    isCommMonObj_condensedRingObj _ V
  let adj := CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction q
  let κ := (mateEquiv adj level.adjunction).symm ρD.hom
  have : (CategoryTheory.Mod.comap a.inv).IsEquivalence :=
    (CategoryTheory.Mod.comapEquivalenceOfIsIso a.inv).isEquivalence_functor
  have : (CategoryTheory.Mod.comap b.inv).IsEquivalence :=
    (CategoryTheory.Mod.comapEquivalenceOfIsIso b.inv).isEquivalence_functor
  have : (integralSections ℓ E V).IsEquivalence :=
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      J _).isEquivalence_functor
  have : EA.IsEquivalence := inferInstanceAs
    (CategoryTheory.Mod.comap a.inv ⋙ integralSections ℓ E V).IsEquivalence
  have : EB.IsEquivalence := inferInstanceAs
    (CategoryTheory.Mod.comap b.inv ⋙
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        J _).functor).IsEquivalence
  have eA := Functor.isEquivalence_mapDerivedCategory EA
  have eB := Functor.isEquivalence_mapDerivedCategory EB
  let adjA := EA.mapDerivedCategory.asEquivalence.toAdjunction
  let adjB := EB.mapDerivedCategory.asEquivalence.toAdjunction
  let β := mateEquiv adjB adjA ρD.hom
  have : IsIso adjA.unit := EA.mapDerivedCategory.asEquivalence.unitIso.isIso_hom
  have : IsIso adjB.counit := EB.mapDerivedCategory.asEquivalence.counitIso.isIso_hom
  have hβiso : IsIso β := by
    change IsIso (mateEquiv adjB adjA ρD.hom)
    rw [mateEquiv_apply]
    infer_instance
  -- The mate along the encoding equivalences is invertible. Its conjugate detects κ.
  have hκ := iterated_mateEquiv_conjugateEquiv adj level.adjunction adjA adjB κ
  have hρD := (mateEquiv adj level.adjunction).apply_symm_apply ρD.hom
  have hk := (congrArg (mateEquiv adjB adjA) hρD.symm).trans hκ
  have : IsIso κ := @conjugateEquiv_of_iso _ _ _ _ _ _ _ _
    (adj.comp adjB) (adjA.comp level.adjunction) κ ((congrArg IsIso hk).mp hβiso)
  -- Whisker the evaluation and diagonal isomorphisms in the order used by sectionEvaluation.
  let incl := (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V)).ι
  let M := integralTransport ℓ V
  let inc := (boundedConstructible (internalRing V (Padic.coefficientExtensionIntegers ℓ E))).ι
  let Z := (M ⋙ inc) ⋙ (integralSections ℓ E V).mapDerivedCategory
  let Δ := derivedConstantSystem.{u + 1, u, u + 1} J
    (sectionRing V (Padic.coefficientExtensionIntegers ℓ E))
  let cmp :=
    Functor.mapDerivedCategoryCompIso (CategoryTheory.Mod.comap a.inv) (integralSections ℓ E V)
  let diag := Functor.isoWhiskerLeft Z (diagonalEvaluation ℓ V n) ≪≫ Functor.isoWhiskerLeft incl cmp
  let ev :=
    Functor.isoWhiskerLeft (M ⋙ reductionBc ℓ E V) (FiniteProEtaleSystem.evaluationIso ℓ V n) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Z ⋙ Δ) (sys.evaluation n) ≪≫
      Functor.isoWhiskerRight diag level.T) H.mapDerivedCategory
  let k := Functor.isoWhiskerLeft incl (asIso κ)
  let θ := Functor.isoWhiskerRight (ev ≪≫ Functor.isoWhiskerRight k H.mapDerivedCategory)
    G.mapDerivedCategory ≪≫ Functor.isoWhiskerLeft (red ⋙ (boundedConstructible _).ι) σD
  refine ⟨θ, ρ, σ, hρ, hσ, ?_⟩
  intro ρ' σ' level' K X Y ι η k'
  -- The bounded inclusion comparison is the identity on the underlying derived object.
  have hη : η = adj.unit.app X := by
    exact (congrArg (fun t ↦ t ≫ (CategoryTheory.Mod.comap q).mapDerivedCategory.map ι)
      (canonicalReductionTowerCone_π_app ℚ_[ℓ] X n)).trans <|
      (congrArg (adj.unit.app X ≫ ·)
        ((CategoryTheory.Mod.comap q).mapDerivedCategory.map_id Y)).trans (Category.comp_id _)
  have ht : κ.app X = k' :=
    (level.adjunction.homEquiv _ _).eq_symm_apply.mpr <|
      (unit_mateEquiv_symm adj level.adjunction ρD.hom X).symm.trans
        (congrArg (fun f ↦ EA.mapDerivedCategory.map f ≫ ρD.hom.app Y) hη.symm)
  exact congrArg (fun f ↦ G.mapDerivedCategory.map
    ((sectionEvaluation ℓ V n K).hom ≫ H.mapDerivedCategory.map f) ≫ σD.hom.app Y) ht

end WeilII.CoherentIntegralEvaluation
