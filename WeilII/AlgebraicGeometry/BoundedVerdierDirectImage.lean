module

public import WeilConjectures.PoincareDuality.Biduality.Constructible
import WeilII.AlgebraicGeometry.VerdierExchangeNaturality

/-! # Verdier exchange for the two direct images on bounded constructible complexes -/

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

universe u

namespace WeilII

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- Use the published tensor–Hom adjunction on the bounded category. -/
private noncomputable abbrev boundedClosed (Z : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] :
    MonoidalClosed (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) where
  closed K := { rightAdj := (boundedConstructibleHom ℓ Z).obj (Opposite.op K)
                adj := boundedConstructibleTensorHomAdjunction (X := Z) ℓ K }

/-- Relative Verdier exchange for a fixed target is natural in the source complex. -/
public noncomputable def boundedVerdierExchangeIso
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleHom ℓ X).flip.obj ((boundedConstructibleUpperShriek ℓ f).obj L) ⋙
        boundedConstructibleLowerStar ℓ f ≅
      (boundedConstructibleLowerShriek ℓ f).op ⋙ (boundedConstructibleHom ℓ Y).flip.obj L := by
  letI := boundedClosed ℓ X
  letI := boundedClosed ℓ Y
  exact NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ _ (isIso_verdierExchange ℓ f K.unop L))
    (fun g ↦ verdierExchange_naturality (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ f) (boundedConstructibleExceptionalProjection ℓ f)
      g.unop L)

private noncomputable def bidualIso (Z : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] :
    let D := (boundedConstructibleHom ℓ Z).flip.obj (dualizingComplex ℓ Z)
    𝟭 _ ≅ D.rightOp ⋙ D := by
  letI := boundedClosed ℓ Z
  letI := boundedConstructibleBraiding (ℓ := ℓ) Z
  exact NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ _ (isIso_verdierBiduality ℓ M))
    (fun h ↦ toIhomIhom_naturality (dualizingComplex ℓ Z) h)

/-- The Verdier dual of the ordinary direct image is the exceptional direct image of
the Verdier dual, naturally for bounded constructible coefficients. -/
public noncomputable def boundedVerdierStarDualIso :
    (boundedConstructibleLowerStar ℓ f).op ⋙
        (boundedConstructibleHom ℓ Y).flip.obj (dualizingComplex ℓ Y) ≅
      (boundedConstructibleHom ℓ X).flip.obj (dualizingComplex ℓ X) ⋙
        boundedConstructibleLowerShriek ℓ f := by
  let DX := (boundedConstructibleHom ℓ X).flip.obj (dualizingComplex ℓ X)
  let DY := (boundedConstructibleHom ℓ Y).flip.obj (dualizingComplex ℓ Y)
  let G := boundedConstructibleLowerStar ℓ f
  let P := boundedConstructibleLowerShriek ℓ f
  let ex : DX ⋙ G ≅ P.op ⋙ DY :=
    Functor.isoWhiskerRight ((boundedConstructibleHom ℓ X).flip.mapIso
      (upperShriekDualizingComplexIso ℓ f).symm) G ≪≫ boundedVerdierExchangeIso ℓ f _
  let u : G ≅ DX.rightOp ⋙ P.op ⋙ DY := Functor.isoWhiskerRight (bidualIso ℓ X) G ≪≫
    Functor.isoWhiskerLeft DX.rightOp ex
  exact Functor.isoWhiskerRight (NatIso.op u.symm) DY ≪≫
    Functor.isoWhiskerLeft (DX ⋙ P) (bidualIso ℓ Y).symm

end WeilII
