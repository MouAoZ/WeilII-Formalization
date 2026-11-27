module

public import WeilII.AlgebraicGeometry.CompactSupportTerminalFrobenius
meta import WeilConjectures.Tactic.ExactByKernel

/-! # Frobenius squares of compact-support images under the bounded inclusion -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

open CompactSupportClasses

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

universe u
variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
local notation "Ω" => AlgebraicClosure k
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
private instance : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
private instance : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

private theorem underlyingRestrictionSquare
    {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
    (F : C ⥤ C) [F.Monoidal] (pres : ∀ A : P.FullSubcategory, P (F.obj A.obj))
    (A B T : P.FullSubcategory) :
    let G := P.lift (P.ι ⋙ F) pres
    ∀ (a : G.obj A ⟶ A) (b : G.obj B ⟶ B) (z : G.obj T ⟶ T) (γ : A ⊗ B ⟶ T)
      (a' : F.obj A.obj ⟶ A.obj) (b' : F.obj B.obj ⟶ B.obj) (z' : F.obj T.obj ⟶ T.obj),
      a' = a.hom → b' = b.hom → z' = z.hom →
      G.map γ ≫ z = Functor.OplaxMonoidal.δ G A B ≫ (a ⊗ₘ b) ≫ γ →
      F.map γ.hom ≫ z' = Functor.OplaxMonoidal.δ F A.obj B.obj ≫ (a' ⊗ₘ b') ≫ γ.hom := by
  intro G a b z γ a' b' z' ha hb hz square
  subst a' b' z'
  exact congrArg (fun w ↦ w.hom) square

/-- The bounded inclusion takes an equivariant map out of the tensor of two compact-support
images to an equivariant map of ambient complexes. Both the pullback and its tensor comparison
are restrictions of the ambient ones. For each of the three sheaves the canonical bounded
image structure maps to the ambient image structure by `imageFrobenius_eq_mapIso_at`. -/
public theorem compactSupportImageFrobenius_of_boundedSquare
    {X Y P : Over (Spec (.of k))}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    (L : WeilSheaf k ℓ X.left) (M : WeilSheaf k ℓ Y.left) (N : WeilSheaf k ℓ P.left) :
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) (point Ω)).toMonoidalCategoryStruct
    let f := toPoint (geometricFiberOver X)
    let g := toPoint (geometricFiberOver Y)
    let a := toPoint (geometricFiberOver P)
    let fH := boundedConstructibleLowerShriek ℓ f
    let gH := boundedConstructibleLowerShriek ℓ g
    let K := carrier.obj L
    let J := carrier.obj M
    let u := (purityFieldLowerShriekBaseChange ℓ f f (isPullback_frobenius_terminalMap f)).hom.app K
    let v := (purityFieldLowerShriekBaseChange ℓ g g (isPullback_frobenius_terminalMap g)).hom.app J
    let x := fH.map (carrierFrobenius L).hom
    let y := gH.map (carrierFrobenius M).hom
    let z := (imageFrobeniusAt (Z := P) N a).hom
    let σ := (specGeometricFrobenius k).asIso.hom
    let G := boundedConstructibleUpperStarOfMap ℓ (X := point Ω) (Y := point Ω) σ
    let F := pull (ℓ := ℓ) σ
    letI : F.Monoidal := monoidal_leftDerivedUpperStar Λ σ
    ∀ γ : fH.obj K ⊗ gH.obj J ⟶ (boundedConstructibleLowerShriek ℓ a).obj (carrier.obj N),
      G.map γ ≫ z = Functor.OplaxMonoidal.δ G (fH.obj K) (gH.obj J) ≫
        ((u ≫ x) ⊗ₘ (v ≫ y)) ≫ γ →
      F.map γ.hom ≫ (imageFrobenius N).hom = Functor.OplaxMonoidal.δ F _ _ ≫
        ((imageFrobenius L).hom ⊗ₘ (imageFrobenius M).hom) ≫ γ.hom := by
  intro f g a fH gH K J u v x y z σ G F γ bounded
  let _ : F.Monoidal := monoidal_leftDerivedUpperStar Λ σ
  let Ef := purityFieldLowerShriekBaseChange ℓ f f (isPullback_frobenius_terminalMap f)
  let Eg := purityFieldLowerShriekBaseChange ℓ g g (isPullback_frobenius_terminalMap g)
  have ha : imageFrobeniusAt (Z := X) L f = Ef.app K ≪≫ fH.mapIso (carrierFrobenius L) := rfl
  have hb : imageFrobeniusAt (Z := Y) M g = Eg.app J ≪≫ gH.mapIso (carrierFrobenius M) := rfl
  have hL' : (imageFrobenius L).hom = (u ≫ x).hom := by
    have hi := (imageFrobenius_eq_mapIso_at (Z := X) L).trans
      (congrArg (Functor.mapIso (boundedConstructible _).ι) ha)
    exact_by_kernel congrArg Iso.hom hi
  have hM' : (imageFrobenius M).hom = (v ≫ y).hom := by
    have hi := (imageFrobenius_eq_mapIso_at (Z := Y) M).trans
      (congrArg (Functor.mapIso (boundedConstructible _).ι) hb)
    exact_by_kernel congrArg Iso.hom hi
  have hN' : (imageFrobenius N).hom = z.hom := by
    exact_by_kernel congrArg Iso.hom (imageFrobenius_eq_mapIso_at (Z := P) N)
  have ambient := underlyingRestrictionSquare (boundedConstructible (condensedRingObj Λ (point Ω).left))
    F (fun A ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ σ A.obj A.property)
    (fH.obj K) (gH.obj J) ((boundedConstructibleLowerShriek ℓ a).obj (carrier.obj N)) (u ≫ x) (v ≫ y) z γ
    (imageFrobenius L).hom (imageFrobenius M).hom (imageFrobenius N).hom hL' hM' hN' bounded
  exact_by_kernel ambient

end WeilII
