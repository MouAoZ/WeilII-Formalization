module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
import WeilConjectures.TraceFormula.WeilBaseChange
import WeilII.AlgebraicGeometry.SlicePullbackComposition
import WeilII.AlgebraicGeometry.CompactificationComponentTransport

/-! # The compact-support base-change cube in one field slice -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

private theorem unpaste {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {M N : A} (e : M ≅ N) {D₀ D₁ D₂ : B} (a : D₀ ⟶ D₁) (b : D₁ ⟶ D₂) (c : D₂ ⟶ F.obj N)
    (t : D₀ ⟶ F.obj M) (ht : t = a ≫ b ≫ c ≫ F.map e.inv) :
    a ≫ b ≫ c = t ≫ F.map e.hom := by
  subst t
  simp [Category.assoc, ← F.map_comp]

/-- Compare two cartesian faces by cartesian connecting faces in a field slice.
Paste through the first projection and through the second structure map. Both pastings
give the same outer base-change component through the casts of the two equal composite
arrows. Cancelling the pullback composition constraints gives the cube. This is the
two-rectangle argument of `TraceFormula/WeilBaseChange.lean`, with distinct end vertices. -/
private theorem component_cube
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)]
    {P X Y S P' X' Y' S' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
    {s : P ⟶ Y} {p : P ⟶ X} {g : Y ⟶ S} {f : X ⟶ S} (sq : IsPullback s p g f)
    {s' : P' ⟶ Y'} {p' : P' ⟶ X'} {g' : Y' ⟶ S'} {f' : X' ⟶ S'} (sq' : IsPullback s' p' g' f')
    (tP : P' ⟶ P) (tX : X' ⟶ X) (tY : Y' ⟶ Y) (tS : S' ⟶ S)
    (hs : CommSq tP s' s tY) (hp : IsPullback tP p' p tX)
    (hg : IsPullback tY g' g tS) (hf : CommSq tX f' f tS)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tX).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app L) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hp).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s).obj L) ≫
      (boundedConstructibleLowerShriek ℓ p').map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ tP s).inv.app L ≫
          eqToHom (congrArg (fun t ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ t).obj L) hs.w) ≫
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ s' tY).hom.app L) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ tX f).inv.app
          ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        eqToHom (congrArg (fun t ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ t).obj
          ((boundedConstructibleLowerShriek ℓ g).obj L)) hf.w) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f' tS).hom.app
          ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hg).app L) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq').app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tY).obj L) := by
  have h₁ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ hp sq L
  have h₂ := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ sq' hg L
  have key : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tX).map
      ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app L) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hp).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s).obj L) ≫
      (boundedConstructibleLowerShriek ℓ p').map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ tP s).inv.app L) =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ tX f).inv.app
        ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (hp.paste_horiz sq)).app L := by
    rw [h₁, Iso.inv_hom_id_app_assoc]
  have key' : (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f' tS).hom.app
          ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hg).app L) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq').app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tY).obj L) =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq'.paste_horiz hg)).app L ≫
        (boundedConstructibleLowerShriek ℓ p').map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ s' tY).hom.app L) := by
    exact unpaste (boundedConstructibleLowerShriek ℓ p')
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ s' tY).app L)
      _ _ _ _ h₂
  simp only [Functor.map_comp]
  rw [reassoc_of% key, reassoc_of% boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_comp_map_eqToHom
    ℓ (hp.paste_horiz sq) (sq'.paste_horiz hg) hs.w hf.w L, key']


/-- Compare two cartesian faces by cartesian connecting faces in a field slice.
Paste through the first projection and through the second structure map. Both pastings
give the same outer base-change component through the casts of the two equal composite
arrows. Cancelling the pullback composition constraints gives the cube. This is the
two-rectangle argument of `TraceFormula/WeilBaseChange.lean`, with distinct end vertices. -/
public theorem shriekBaseChange_sliceCube
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)]
    {P X Y S P' X' Y' S' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
    {s : P ⟶ Y} {p : P ⟶ X} {g : Y ⟶ S} {f : X ⟶ S} (sq : IsPullback s p g f)
    {s' : P' ⟶ Y'} {p' : P' ⟶ X'} {g' : Y' ⟶ S'} {f' : X' ⟶ S'} (sq' : IsPullback s' p' g' f')
    (tP : P' ⟶ P) (tX : X' ⟶ X) (tY : Y' ⟶ Y) (tS : S' ⟶ S)
    (hs : CommSq tP s' s tY) (hp : IsPullback tP p' p tX)
    (hg : IsPullback tY g' g tS) (hf : CommSq tX f' f tS)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tX).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app L) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hp).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s).obj L) ≫
      (boundedConstructibleLowerShriek ℓ p').map
        ((boundedConstructibleUpperStarOfMapSquareIso ℓ s s'
          (Over.left_comp_left_eq_of_comp_eq hs.w)).hom.app L) =
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f'
          (Over.left_comp_left_eq_of_comp_eq hf.w)).hom.app
          ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hg).app L) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq').app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ tY).obj L) := by
  have h := component_cube ℓ sq sq' tP tX tY tS hs hp hg hf L
  rw [upperStarOfMapSquare_slice_app ℓ hs, upperStarOfMapSquare_slice_app ℓ hf]
  dsimp only [boundedConstructibleUpperStarOfMap, boundedConstructibleUpperStar,
    Functor.comp_obj] at h ⊢
  simp only [Category.assoc]
  transport_compactification_component h

end WeilII
