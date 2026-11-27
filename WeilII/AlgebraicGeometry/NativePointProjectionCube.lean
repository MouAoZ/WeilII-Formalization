module

public import WeilII.AlgebraicGeometry.ShriekBaseChangeUnderSchemeIsomorphisms
import WeilII.AlgebraicGeometry.UnderlyingSchemePullbackSquareComponent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangeCoherence
import WeilII.AlgebraicGeometry.ShriekBaseChangeChangePrimedStructure
meta import WeilConjectures.Tactic.ExactByKernel
meta import WeilII.Tactic.SchemeComponentCongruence

/-! # Shriek exchange for the projection of the native geometric point -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

/-- For a weakly étale base change in one field slice, the exchange for the chosen
Nagata compactification equals the cross-field exchange for the underlying arrows. -/
public theorem sliceShriekBaseChange_eq_underlying {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    [WeaklyEtale y.left] (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K =
      (purityFieldLowerShriekBaseChange ℓ f f' sq.overLeft).hom.app K := by
  have : LocallyOfFiniteType (Over.mk U'.hom).hom := ‹LocallyOfFiniteType U'.hom›
  have : QuasiCompact (Over.mk U'.hom).hom := ‹QuasiCompact U'.hom›
  have : IsSeparated (Over.mk U'.hom).hom := ‹IsSeparated U'.hom›
  have : LocallyOfFiniteType (Over.mk V'.hom).hom := ‹LocallyOfFiniteType V'.hom›
  have : QuasiCompact (Over.mk V'.hom).hom := ‹QuasiCompact V'.hom›
  have : IsSeparated (Over.mk V'.hom).hom := ‹IsSeparated V'.hom›
  let E := purityFieldLowerShriekBaseChange ℓ f f' sq.overLeft
  have h := sliceBaseChange_changePrimedStructure ℓ f f' (a := U'.hom) (b := V'.hom) f'.w
    (x := x) (y := y) (p' := f') (by ext; rfl) sq E rfl K
  apply eq_of_heq
  exact_by_kernel h

/-- The base-change cube, with all four base changes expressed in the field convention.
Apply the slice cube and replace its front and back components by their underlying exchanges. -/
public theorem fieldShriekBaseChangeUnderSchemeIsomorphisms
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
    (tP : P'.left ≅ P.left) (tX : X'.left ≅ X.left)
    (tY : Y'.left ≅ Y.left) (tS : S'.left ≅ S.left)
    (hs : CommSq tP.hom s'.left s.left tY.hom) (hp : CommSq tP.hom p'.left p.left tX.hom)
    (hg : CommSq tY.hom g'.left g.left tS.hom) (hf : CommSq tX.hom f'.left f.left tS.hom)
    [WeaklyEtale f.left] [WeaklyEtale f'.left]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let FX := boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') tX.hom
    let FY := boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') tY.hom
    let Ep := purityFieldLowerShriekBaseChange ℓ p p' (IsPullback.of_horiz_isIso hp)
    let Eg := purityFieldLowerShriekBaseChange ℓ g g' (IsPullback.of_horiz_isIso hg)
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s s' hs.w
    let Df := boundedConstructibleUpperStarOfMapSquareIso ℓ f f' hf.w
    let sStar := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s
    let fStar' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f'
    FX.map ((purityFieldLowerShriekBaseChange ℓ g p sq.overLeft).hom.app L) ≫
        Ep.hom.app (sStar.obj L) ≫ (boundedConstructibleLowerShriek ℓ p').map (Ds.hom.app L) =
      Df.hom.app ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        fStar'.map (Eg.hom.app L) ≫
        (purityFieldLowerShriekBaseChange ℓ g' p' sq'.overLeft).hom.app (FY.obj L) := by
  intro FX FY Ep Eg Ds Df sStar fStar'
  have left := sliceShriekBaseChange_eq_underlying ℓ sq L
  have right := sliceShriekBaseChange_eq_underlying ℓ sq' (FY.obj L)
  have cube := shriekBaseChangeUnderSchemeIsomorphisms ℓ sq sq' tP tX tY tS hs hp hg hf L
  have last := congrArg (fun m ↦ Df.hom.app ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
    fStar'.map (Eg.hom.app L) ≫ m) right
  have first := congrArg (fun m ↦ FX.map m ≫ Ep.hom.app (sStar.obj L) ≫
    (boundedConstructibleLowerShriek ℓ p').map (Ds.hom.app L)) left.symm
  dsimp only at cube
  refine first.trans (Eq.trans ?_ last)
  scheme_component_exact cube using hf

private theorem normalizeProjectionCube {C B D : Type*} [Category* C] [Category* B] [Category* D]
    {F s : C ⥤ C} {H : D ⥤ D} {A : B ⥤ B} {g : C ⥤ B} {p : C ⥤ D} {y : B ⥤ D}
    (E : g ⋙ y ⟶ s ⋙ p) (Ep : p ⋙ H ⟶ F ⋙ p) (Eg : g ⋙ A ⟶ F ⋙ g)
    (Ds : s ⋙ F ⟶ F ⋙ s) (Df : y ⋙ H ⟶ A ⋙ y) (i : s ⟶ 𝟭 C) (K : C) (v : F.obj K ⟶ K)
    (idSq : Ds.app K ≫ i.app (F.obj K) = F.map (i.app K))
    (cube : H.map (E.app K) ≫ Ep.app (s.obj K) ≫ p.map (Ds.app K) =
      Df.app (g.obj K) ≫ y.map (Eg.app K) ≫ E.app (F.obj K)) :
    H.map (E.app K ≫ p.map (i.app K)) ≫ Ep.app K ≫ p.map v =
      (Df.app (g.obj K) ≫ y.map (Eg.app K ≫ g.map v)) ≫ E.app K ≫ p.map (i.app K) := by
  have ep := Ep.naturality (i.app K)
  have e := E.naturality v
  have iv := i.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at ep e iv
  calc
    _ = (H.map (E.app K) ≫ Ep.app (s.obj K) ≫ p.map (Ds.app K)) ≫
        p.map (i.app (F.obj K) ≫ v) := by
      simp only [Functor.map_comp, Category.assoc, reassoc_of% ep, ← idSq]
    _ = _ := by
      rw [cube, ← iv]
      simp only [Functor.map_comp, Category.assoc, reassoc_of% e]

/-- The identity pullback comparison on the bounded category. -/
@[expose] public noncomputable def boundedIdentityPullback {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (U : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 U) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((CondensedRing.leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) U.left).app K.obj))
    (fun v ↦ ObjectProperty.hom_ext _ ((CondensedRing.leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) U.left).hom.naturality v.hom))

private theorem boundedIdentityPullback_square {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (U : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (p : U.left ⟶ U.left)
    (s : CommSq p (𝟙 U.left) (𝟙 U.left) p) (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let F := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) p
    let i := boundedIdentityPullback ℓ U
    let d := boundedConstructibleUpperStarOfMapSquareIso ℓ (𝟙 U) (𝟙 U) s.w
    d.hom.app K ≫ i.hom.app (F.obj K) = F.map (i.hom.app K) := by
  intro F i d
  apply (cancel_epi (d.inv.app K)).1
  refine (d.inv_hom_id_app_assoc K (i.hom.app (F.obj K))).trans ?_
  apply ObjectProperty.hom_ext
  let L := (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p).leftDerivedFunctor
  let u := leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) U.left
  change u.hom.app (L.obj K.obj) = (d.inv.app K).hom ≫ L.map (u.hom.app K.obj)
  have h := (underlyingSchemePullbackComparison_inv_app_hom ℓ (𝟙 U) (𝟙 U) s K).trans
    (pullbackSquareComparison_hom_app_id_right _ p s K.obj)
  change (d.inv.app K).hom = u.hom.app (L.obj K.obj) ≫ L.map (u.inv.app K.obj) at h
  let b := u.hom.app (L.obj K.obj)
  let V := L.mapIso (u.app K.obj)
  exact ((congrArg (· ≫ V.hom) h).trans ((Category.assoc b V.inv V.hom).trans
    ((congrArg (b ≫ ·) V.inv_hom_id).trans (Category.comp_id b)))).symm

/-- Forgetting the forward bounded pullback-square component gives the inverse
ambient comparison. This follows by taking inverses of the component identification. -/
public theorem underlyingSchemePullbackComparison_hom_app_hom
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Y : Over (Spec (.of k))} {X' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (f' : X' ⟶ Y') {p : X'.left ⟶ X.left} {q : Y'.left ⟶ Y.left}
    (s : CommSq p f'.left f.left q) (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapSquareIso ℓ f f' s.w).hom.app B).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) s).inv.app B.obj := by
  let D := boundedConstructibleUpperStarOfMapSquareIso ℓ f f' s.w
  let V := (boundedConstructible _).ι.mapIso (D.app B)
  let W := (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) s).symm.app B.obj
  have hinv : V.inv = W.inv := underlyingSchemePullbackComparison_inv_app_hom ℓ f f' s B
  exact congrArg Iso.inv (Iso.ext (by exact hinv) : V.symm = W.symm)

/-- Transport equivariance across an isomorphism of the acting endofunctors. -/
private theorem changeAction {C : Type*} [Category* C] {U V : C ⥤ C}
    (t : U ≅ V) {A B : C} (a : U.obj A ⟶ A) (b : U.obj B ⟶ B) (m : A ⟶ B)
    (h : U.map m ≫ b = a ≫ m) :
    IsWeilEquivariant V (t.inv.app A ≫ a) (t.inv.app B ≫ b) m := by
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b) (t.inv.naturality m)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans (Category.assoc _ _ _).symm)))

section Projection

variable {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] {U T S : Over (Spec (.of Ω))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

/-- Projecting along a weakly étale base is compatible with automorphisms preserving the
triangle, for any coefficient map from its pullback. Paste the base-change cube and
normalize the identity edge on the coefficient scheme. On the base edge the bounded
comparison has underlying morphism equal to the inverse ambient pullback comparison.
Changing coordinates at the target then follows by naturality. -/
public theorem projectionShriekEquivariance (f : U ⟶ T) (g : U ⟶ S) (y : T ⟶ S)
    (sq : IsPullback (𝟙 U) f g y) [WeaklyEtale y.left]
    (xF : U.left ≅ U.left) (yF : T.left ≅ T.left) (gF : S.left ≅ S.left)
    (hp : CommSq xF.hom f.left f.left yF.hom) (hg : CommSq xF.hom g.left g.left gF.hom)
    (hf : CommSq yF.hom y.left y.left gF.hom) (K : Dᵇc(U.left)⟦Λ⟧)
    (v : (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) xF.hom).obj K ⟶ K)
    (t : (CondensedRing.upperStar Λ yF.hom).leftDerivedFunctor ≅
      (CondensedRing.lowerStar Λ yF.inv).mapDerivedCategory) :
    let V := (CondensedRing.lowerStar Λ yF.inv).mapDerivedCategory
    let Ep := purityFieldLowerShriekBaseChange ℓ f f (IsPullback.of_horiz_isIso hp)
    let Eg := purityFieldLowerShriekBaseChange ℓ g g (IsPullback.of_horiz_isIso hg)
    let E := purityFieldLowerShriekBaseChange ℓ g f sq.overLeft
    let i := boundedIdentityPullback ℓ U
    let Hf := boundedConstructibleLowerShriek ℓ f
    let Hg := boundedConstructibleLowerShriek ℓ g
    let Pa := (CondensedRing.upperStar Λ y.left).leftDerivedFunctor
    IsWeilEquivariant V
      ((t.inv.app _ ≫ (pullbackSquareComparison Λ hf).inv.app (Hg.obj K).obj) ≫
        Pa.map (Eg.hom.app K ≫ Hg.map v).hom)
      (t.inv.app _ ≫ (Ep.hom.app K ≫ Hf.map v).hom)
      (E.hom.app K ≫ Hf.map (i.hom.app K)).hom := by
  intro V Ep Eg E i Hf Hg Pa
  let s := 𝟙 U
  let hs : CommSq xF.hom s.left s.left xF.hom := ⟨by simp [s]⟩
  let FX := boundedConstructibleUpperStarOfMap ℓ (X := T) (Y := T) yF.hom
  let P := boundedConstructibleUpperStar Λ ℓ y
  let Df := boundedConstructibleUpperStarOfMapSquareIso ℓ y y hf.w
  let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s s hs.w
  let mb := E.hom.app K ≫ Hf.map (i.hom.app K)
  let gb := Eg.hom.app K ≫ Hg.map v
  let nb := Ep.hom.app K ≫ Hf.map v
  have bounded : FX.map (E.hom.app K ≫ Hf.map (i.hom.app K)) ≫ Ep.hom.app K ≫ Hf.map v =
      (Df.hom.app (Hg.obj K) ≫ P.map (Eg.hom.app K ≫ Hg.map v)) ≫ E.hom.app K ≫ Hf.map (i.hom.app K) := by
    let F := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) xF.hom
    let A := boundedConstructibleUpperStarOfMap ℓ (X := S) (Y := S) gF.hom
    let S := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) s.left
    refine normalizeProjectionCube (F := F) (s := S) (H := FX) (A := A) (g := Hg)
      (p := Hf) (y := P) E.hom Ep.hom Eg.hom Ds.hom Df.hom i.hom K v ?_ ?_
    · have h := boundedIdentityPullback_square ℓ U xF.hom hs K
      dsimp only at h
      scheme_component_exact h using hf
    · have cube := fieldShriekBaseChangeUnderSchemeIsomorphisms ℓ sq sq xF yF xF gF hs hp hg hf K
      dsimp only at cube
      scheme_component_exact cube using hf
  let m := mb.hom
  let b := nb.hom
  let a := Pa.map gb.hom
  let n := (pullbackSquareComparison Λ hf).inv.app (Hg.obj K).obj
  let Pull := (CondensedRing.upperStar Λ yF.hom).leftDerivedFunctor
  have dd : (Df.hom.app (Hg.obj K)).hom = n :=
    underlyingSchemePullbackComparison_hom_app_hom ℓ y y hf (Hg.obj K)
  have h : Pull.map m ≫ b = ((Df.hom.app (Hg.obj K)).hom ≫ a) ≫ m := by
    exact congrArg (boundedConstructible (condensedRingObj Λ T.left)).ι.map bounded
  have hh := h.trans (congrArg (fun x ↦ (x ≫ a) ≫ m) dd)
  have equiv := changeAction t (n ≫ a) b m hh
  exact (congrArg (fun x ↦ IsWeilEquivariant V x (t.inv.app _ ≫ b) m)
    (Category.assoc (t.inv.app _) n a)).mpr equiv

end Projection
end WeilII
