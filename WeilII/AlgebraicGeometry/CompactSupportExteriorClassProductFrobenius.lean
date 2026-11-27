module

public import WeilII.AlgebraicGeometry.CompactSupportExteriorClassProduct
import WeilII.AlgebraicGeometry.GeometricCompactSupportKunnethFrobenius
import WeilII.AlgebraicGeometry.CompactSupportKunnethImageFrobenius
import WeilII.AlgebraicGeometry.GeometricPointShiftedUnitTensorPullback

/-! # Frobenius on the compact-support exterior product -/

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace WeilII

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

private theorem pasteExterior {C : Type*} [Category* C] [MonoidalCategory C]
    (F : C ⥤ C) [F.OplaxMonoidal] {U V W A B D : C}
    (i : U ⟶ F.obj U) (j : V ⟶ F.obj V) (k : W ⟶ F.obj W)
    (l : F.obj A ⟶ A) (m : F.obj B ⟶ B) (n : F.obj D ⟶ D)
    (s : W ⟶ MonoidalCategory.tensorObj U V) (g : MonoidalCategory.tensorObj A B ⟶ D)
    (hs : k ≫ F.map s ≫ Functor.OplaxMonoidal.δ F _ _ = s ≫ MonoidalCategory.tensorHom i j)
    (hg : F.map g ≫ n = Functor.OplaxMonoidal.δ F _ _ ≫ MonoidalCategory.tensorHom l m ≫ g)
    (u : U ⟶ A) (v : V ⟶ B) :
    k ≫ F.map (s ≫ MonoidalCategory.tensorHom u v ≫ g) ≫ n =
      s ≫ MonoidalCategory.tensorHom (i ≫ F.map u ≫ l) (j ≫ F.map v ≫ m) ≫ g := by
  simp only [F.map_comp, Category.assoc, hg, ← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [← Category.assoc k, ← Category.assoc (k ≫ F.map s), Category.assoc k, hs]
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc]

open AlgebraicGeometry.ProEtale.CondensedRing in
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances in
set_option maxSynthPendingDepth 12 in
private noncomputable abbrev pointMonoidal (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type*) [Field Ω] :
    MonoidalCategory (DerivedCategory (PointMod ℓ Ω)) := inferInstance

set_option maxHeartbeats 1600000 in
/-- Geometric Frobenius sends an exterior product of two compactly supported classes to
the exterior product of their Frobenius images.

Proof (SGA 4, XVII, 5.4.3.2, and Zhang, p. 2). Apply the shifted-unit comparison to both
sides, which is injective. In the image, the exterior product is the splitting of the
shifted unit followed by the tensor of the two representatives and the compact-support
Künneth morphism. The shifted-unit Frobenius formula pulls this composite back along
geometric Frobenius and postcomposes it with the image Weil structure. On the split unit,
pullback gives the same map after its unit and shift identifications. Indeed the tensor
constraint commutes with shifts separately in each variable, the shift constraints commute
with the addition of shifts, and the monoidal unit axiom identifies the remaining unitor.
Naturality of the tensor constraint now moves the pullbacks to the two representatives.
The base-change square for inverse Künneth moves the pullback past Künneth. Coefficient
naturality then moves the two carrier Weil isomorphisms back across that map. The
evaluation-normalized coefficient isomorphism used by the exterior product intertwines them
with the product Weil structure by uniqueness of normalization. The remaining maps on the
two factors are precisely the shifted-unit formulas for the two native Frobenius images. -/
public theorem compactSupportExteriorClassProduct_frobenius
    {k : Type*} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y P : Over (Spec (.of k))}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    (p : P ⟶ X) (s : P ⟶ Y) (product : IsPullback s.left p.left Y.hom X.hom)
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (hL : L.IsLisse) (hM : M.IsLisse)
    (a b : ℤ) (x : (L.compactlySupportedCohomology a).carrier)
    (y : (M.compactlySupportedCohomology b).carrier) :
    let N := ((WeilSheaf.upperStar p.left).obj L).tensorObj ((WeilSheaf.upperStar s.left).obj M)
      (hL.upperStar p.left)
    (N.compactlySupportedCohomology (a + b)).frobenius
        (compactSupportExteriorClassProduct p s product L M hL hM a b x y) =
      compactSupportExteriorClassProduct p s product L M hL hM a b
        ((L.compactlySupportedCohomology a).frobenius x)
        ((M.compactlySupportedCohomology b).frobenius y) :=
  open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing CompactSupportClasses
    MonoidalCategory in
  open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances in
  set_option synthInstance.maxHeartbeats 100000 in
  set_option maxSynthPendingDepth 12 in
  set_option maxHeartbeats 1600000 in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro N
  delta compactSupportExteriorClassProduct
  extract_lets +usedOnly p' f g K J N' A B comparison coeff sq κ h img toCanonical γ post
  let Ω := AlgebraicClosure k
  let : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
  let : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let := pointMonoidal ℓ Ω
  let ρL := (exists_natural_equiv (X := X.left) a).choose L hL
  let ρM := (exists_natural_equiv (X := Y.left) b).choose M hM
  have hN : N.IsLisse := (hL.upperStar p.left).tensorObj (hM.upperStar s.left)
  let ρN := (exists_natural_equiv (X := P.left) (a + b)).choose N hN
  let grade := (geometricPointGradedTensorKunneth ℓ Ω A B (a + b)).choose
  let i : {q : ℤ × ℤ // q.1 + q.2 = a + b} := ⟨(a, b), rfl⟩
  let val := fun u v ↦ grade (DirectSum.lof (PadicAlgCl ℓ) _ _ i (ρL u ⊗ₜ[PadicAlgCl ℓ] ρM v))
  let F : DerivedCategory (PointMod ℓ Ω) ⥤ DerivedCategory (PointMod ℓ Ω) :=
    pull (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom
  let ε (j : ℤ) := (pullUnit (ℓ := ℓ) (specGeometricFrobenius k).asIso.hom (-j)).inv
  let split := (geometricPointShiftedUnitTensorIso ℓ Ω (a := a) (b := b) rfl).hom
  change (N.compactlySupportedCohomology (a + b)).frobenius (ρN.symm (post (val x y))) =
    ρN.symm (post (val _ _))
  apply ρN.injective
  rw [LinearEquiv.apply_symm_apply]
  change gradedHomHom ℓ Ω _ = gradedHomHom ℓ Ω _
  rw [(exists_natural_equiv (X := P.left) (a + b)).choose_spec.2.2 N hN,
    ρN.apply_symm_apply]
  have rep (u v) : gradedHomHom ℓ Ω (post (val u v)) =
      split ≫ tensorHom (gradedHomHom ℓ Ω (ρL u)) (gradedHomHom ℓ Ω (ρM v)) ≫ γ.hom := by
    exact (gradedHomHom_map_apply _ _ _ _ _).trans
      ((congrArg (fun z ↦ z ≫ γ.hom)
        ((geometricPointGradedTensorKunneth ℓ Ω A B (a+b)).choose_spec i (ρL u) (ρM v))).trans
        (Category.assoc _ _ _))
  rw [rep, rep, (exists_natural_equiv (X := X.left) a).choose_spec.2.2 L hL,
    (exists_natural_equiv (X := Y.left) b).choose_spec.2.2 M hM]
  let σ := (specGeometricFrobenius k).asIso.hom
  let : F.Monoidal := monoidal_leftDerivedUpperStar (Profinite.padicAlgClRingObj ℓ) σ
  let δ := Functor.OplaxMonoidal.δ F
  have unitSquare : ε (a + b) ≫ F.map split ≫ δ _ _ = split ≫ tensorHom (ε a) (ε b) := by
    exact geometricPointShiftedUnitTensor_pullback ℓ Ω σ a b
  have imageSquare : F.map γ.hom ≫ (imageFrobenius N).hom = δ _ _ ≫
      tensorHom (imageFrobenius L).hom (imageFrobenius M).hom ≫ γ.hom := by
    exact compactSupportKunnethImage_frobenius p s product L M hL sq coeff comparison.choose_spec
  let u := gradedHomHom ℓ Ω (ρL x)
  let v := gradedHomHom ℓ Ω (ρM y)
  exact pasteExterior F (ε a) (ε b) (ε (a + b)) (imageFrobenius L).hom (imageFrobenius M).hom
    (imageFrobenius N).hom split γ.hom unitSquare imageSquare u v

end WeilII
