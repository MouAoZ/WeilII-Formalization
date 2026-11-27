module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Profinite
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import Mathlib.NumberTheory.Padics.RingHoms

/-! # The underlying ordinary quotient tower of the integral regular module -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor


namespace WeilII

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- At the ground coefficient field, the native positive-power quotients are exactly
the residue rings of the p-adic integers. Restrict the identity on the field to the
unit balls using preservation of the norm. Transport the principal ideal of the
power and apply the first isomorphism theorem for the p-adic reduction map. -/
def groundQuotientRingEquiv (m : ℕ) :
    ZMod (ℓ ^ m) ≃+* PadicAlgCl.integersModPow ℓ ℚ_[ℓ] m := by
  let I := PadicAlgCl.integers ℓ ℚ_[ℓ]
  let e := (RingEquiv.refl ℚ_[ℓ]).restrict (PadicInt.subring ℓ) I.toSubring
    (fun x ↦ by
      change ‖x‖ ≤ 1 ↔ ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) x‖ ≤ 1
      rw [PadicAlgCl.norm_extends])
  let q := PadicInt.toZModPow (p := ℓ) m
  have surj : Function.Surjective q := fun x ↦ ⟨x.val, by simp [q]⟩
  exact (q.quotientKerEquivOfSurjective surj).symm.trans
    (Ideal.quotientEquiv _ _ e (by
      change Ideal.span {(ℓ : I) ^ m} = (RingHom.ker (PadicInt.toZModPow m)).map _
      rw [PadicInt.ker_toZModPow]
      simp [Ideal.map_span]))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ℓ}

/-- Reindexing finite constant coefficients by a ring homomorphism commutes with
comparison to continuous sections on the profinite point. Both sides take a constant
element to the same constant function. Sheafification and its counit preserve this
identity. -/
theorem pointConstants_naturality {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology A] [DiscreteTopology B] (f : A →+* B) :
    let J := coherentTopology Profinite.{u}
    let p := (sheafCompose J (forget₂ RingCat.{u+1} Ab.{u+1})).map
      (Profinite.continuousMapRingSheafMap f continuous_of_discreteTopology)
    (constantSheaf J Ab.{u+1}).map (uliftAddHom f) ≫ Profinite.constRingSheafToContinuousMapRingObj B =
      Profinite.constRingSheafToContinuousMapRingObj A ≫ p := by
  intro J p
  let L := presheafToSheaf J Ab.{u+1}
  let adj := sheafificationAdjunction J Ab.{u+1}
  have h := adj.counit.naturality p
  change L.map _ ≫ L.map _ ≫ adj.counit.app _ = (L.map _ ≫ adj.counit.app _) ≫ p
  dsimp only [Functor.id_map] at h
  erw [Category.assoc, ← h]
  change L.map _ ≫ L.map _ ≫ _ = L.map _ ≫ L.map _ ≫ _
  rw [← L.map_comp_assoc, ← L.map_comp_assoc]
  rfl

variable (ℓ)

/-- The pro-étale finite coefficient rings form the pullback of the étale tower of
ordinary residue rings. Use the base-field quotient isomorphism at each exponent,
then the constant-sheaf comparison on the profinite point. The two homomorphisms
out of each cyclic residue ring agree since both preserve one. Naturality of constant
sheaves, site pullback, and constant functions then gives the successor squares. -/
def groundCoefficientTowerIso (V : Scheme.{u}) :
    let q := fun n : ℕ ↦ ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n+1))) (ZMod (ℓ^(n+1)))
    constantSheafTower V (Qs := fun n ↦ ZMod (ℓ^(n+1))) q ⋙ comparisonUpperStar Ab.{u+1} V ≅
      Functor.ofOpSequence (X := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj ℓ ℚ_[ℓ] (n+1)) V)
        (fun n ↦ integersModPowTransition V ℓ ℚ_[ℓ] (n+1)) := by
  intro q
  let D := constantSheaf (coherentTopology Profinite.{u}) Ab.{u+1}
  let L := upperStarFromPoint V
  let E := constantSheaf V.smallEtaleTopology Ab.{u+1}
  let P := comparisonUpperStar Ab.{u+1} V
  let j : E ⋙ P ≅ D ⋙ L := constantSheafCompComparisonUpperStarIso Ab.{u+1} V ≪≫ constantSchemeIso V
  let e (n : ℕ) := groundQuotientRingEquiv ℓ (n+1)
  let φ (n : ℕ) := uliftAddHom.{u} (e n).toRingHom
  have hφ (n : ℕ) : IsIso (φ n) := by
    refine ⟨uliftAddHom (e n).symm.toRingHom, ?_, ?_⟩
    · ext x
      exact (e n).symm_apply_apply x.down
    · ext x
      exact (e n).apply_symm_apply x.down
  let c (n : ℕ) := Profinite.constRingSheafToContinuousMapRingObj.{u}
    (PadicAlgCl.integersModPow ℓ ℚ_[ℓ] (n+1))
  let k (n : ℕ) := j.hom.app _ ≫ L.map (D.map (φ n) ≫ c n)
  let t : constantSheafTower V (Qs := fun n ↦ ZMod (ℓ^(n+1))) q ⋙ P ⟶ Functor.ofOpSequence
      (X := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj ℓ ℚ_[ℓ] (n+1)) V)
      (fun n ↦ integersModPowTransition V ℓ ℚ_[ℓ] (n+1)) := NatTrans.ofOpSequence k fun n ↦ by
    let g := PadicAlgCl.integersModPowTransition ℓ ℚ_[ℓ] (n+1)
    let p := Profinite.integersModPowRingObjTransition.{u} ℓ ℚ_[ℓ] (n+1)
    have hg := pointConstants_naturality.{u} g
    have he : (e n).toRingHom.comp (q n) = g.comp (e (n+1)).toRingHom := Subsingleton.elim _ _
    have hh : uliftAddHom.{u} (q n) ≫ φ n = φ (n+1) ≫ uliftAddHom g := by
      ext x
      exact RingHom.congr_fun he x.down
    rw [Functor.comp_map, constantSheafTower_map_succ, Functor.ofOpSequence_map_homOfLE_succ]
    change (E ⋙ P).map _ ≫ j.hom.app _ ≫ L.map _ = (j.hom.app _ ≫ L.map _) ≫ L.map p
    rw [j.hom.naturality_assoc, Category.assoc]
    change _ ≫ L.map (D.map _) ≫ L.map _ = _ ≫ L.map _ ≫ L.map _
    rw [← L.map_comp, ← L.map_comp, ← D.map_comp_assoc, hh, D.map_comp, Category.assoc, hg]
    simp only [Category.assoc]
    rfl
  have ht (n : ℕᵒᵖ) : IsIso (t.app n) := by
    dsimp only [t]
    rw [NatTrans.ofOpSequence_app]
    dsimp only [k]
    have : IsIso (c n.unop) := inferInstanceAs (IsIso (Profinite.constRingSheafToContinuousMapRingObj _))
    infer_instance
  have := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Extension of the integral regular module to all quotients, followed by forgetting
its action, gives the tower of finite coefficient rings with the original quotient maps.
At level m use the inverse of the regular scalar extension isomorphism. Precompose
the successor square with the epimorphism from the integral ring. The two composites
are then the same scalar-extension unit by transitivity of the units. -/
def regularReductionTowerIso (V : Scheme.{u}) :
    let r := fun n : ℕ ↦ integersModPowReduction V ℓ ℚ_[ℓ] (n+1)
    let g := fun n : ℕ ↦ integersModPowTransition V ℓ ℚ_[ℓ] (n+1)
    let F := fun n ↦ Mod.extendScalars (r n) ⋙ Mod.comap (r n)
    let t : ∀ n, F (n+1) ⟶ F n := fun n ↦ Mod.extendComapTransition _ _ _
      (integersModPowReduction_comp_integersModPowTransition V ℓ ℚ_[ℓ] (n+1))
    let A := condensedRingObj (Profinite.padicIntegersRingObj ℓ ℚ_[ℓ]) V
    Functor.ofOpSequence (X := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj
      ℓ ℚ_[ℓ] (n+1)) V) g ≅ ((Functor.ofOpSequence t).flip.obj (Mod.regular A)) ⋙ Mod.forget A := by
  intro r g F t A
  let k (n : ℕ) := (Mod.extendScalarsObjRegularIso (r n)).inv.hom
  let s : Functor.ofOpSequence (X := fun n ↦ condensedRingObj (Profinite.integersModPowRingObj
      ℓ ℚ_[ℓ] (n+1)) V) g ⟶ ((Functor.ofOpSequence t).flip.obj (Mod.regular A)) ⋙ Mod.forget A :=
    NatTrans.ofOpSequence k fun n ↦ by
      have : Epi (r (n+1)) := (shortExact_integersModPowReduction V ℓ ℚ_[ℓ] (n+2)).epi_g
      simp only [Functor.comp_map, Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
      apply (cancel_epi (r (n+1))).mp
      have h (j : ℕ) : r j ≫ k j = Mod.extendUnitHom (r j) (Mod.regular A) :=
        Mod.comp_extendScalarsObjRegularIso_inv_hom (r j)
      have w := Mod.extendRestrictAdjunction_unit_app_comp_extendComapTransition_app
        (r (n+1)) (g n) (r n) (integersModPowReduction_comp_integersModPowTransition V ℓ ℚ_[ℓ] _)
        (Mod.regular A)
      have hg : r (n+1) ≫ g n = r n := integersModPowReduction_comp_integersModPowTransition _ _ _ _
      rw [← Category.assoc, hg, h, ← Category.assoc, h]
      rw [Mod.extendRestrictAdjunction_unit_app, Mod.extendRestrictAdjunction_unit_app] at w
      exact (congrArg (fun f ↦ f.hom) w).symm
  have hs (n : ℕᵒᵖ) : IsIso (s.app n) := by
    dsimp only [s]
    rw [NatTrans.ofOpSequence_app]
    exact Functor.map_isIso (Mod.forget _) (Mod.extendScalarsObjRegularIso (r n.unop)).inv
  have := NatIso.isIso_of_isIso_app s
  exact asIso s

end WeilII
