module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.SeparatedDirectImage

/-!
# Generic base change for a fixed bounded constructible complex with finite coefficients
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

universe u

/-- Deligne's generic base change (SGA 4½, Théorèmes de finitude, 1.9(ii)) for a fixed
bounded constructible complex. The dense open works for every noetherian change of base.

Compactify the morphism and intersect the finitely many opens supplied by Deligne for
the cohomology sheaves along the open immersion. The exchange is invertible on the whole
complex by its finite truncation tower. Proper base change and pasting conclude. -/
public theorem exists_denseOpen_isIso_etaleDerivedBaseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (a : S ⟶ Spec (.of k)) [LocallyOfFiniteType a]
    [QuasiCompact a] [HasInvertibleExponent Λ S] (p : Y ⟶ S)
    [LocallyOfFiniteType p] [QuasiCompact p] (h : X ⟶ Y) [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h]
    (C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X C) :
    ∃ W : S.Opens, Dense (W : Set S) ∧
      ∀ {B : Scheme.{u}} [IsNoetherian B] (s : B ⟶ S), Set.range s ⊆ W →
        ∀ {Ys Xs : Scheme.{u}} {iY : Ys ⟶ Y} {ps : Ys ⟶ B}, IsPullback iY ps p s →
          ∀ {iX : Xs ⟶ X} {hs : Xs ⟶ Ys} (sq : IsPullback iX hs h iY),
            IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app C) :=
  open Etale Scheme in by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (p ≫ a)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ a)
  let c := NagataCompactification h
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hC.1
  let I := Finset.Icc lo hi
  let F (i : ℤ) := (_root_.DerivedCategory.homologyFunctor _ i).obj C
  have hF (i : ℤ) : IsConstructibleSheaf (F i) := hC.2 i
  choose V hV hBC using fun i : I ↦
    exists_hasConstructibleDirectImageBaseChangeOn Λ a (c.g ≫ p) c.i (F i)
  let W := ⨅ i : I, V i
  have hmem (x : S) : x ∈ W ↔ ∀ i, x ∈ V i := by
    change x ∈ ((↑(iInf V) : Set S)) ↔ _
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    rfl
  have hne : (W : Set S).Nonempty := ⟨genericPoint S,
    (hmem _).2 fun i ↦ genericPoint_mem_of_nonempty _ (hV i)⟩
  refine ⟨W, W.isOpen.dense hne, ?_⟩
  intro B _ s hsW Ys Xs iY ps sy iX hs sq
  have hp : IsPullback (pullback.fst c.g iY) (pullback.snd c.g iY) c.g iY :=
    .of_hasPullback _ _
  let j := pullback.lift (iX ≫ c.i) hs (by rw [Category.assoc, ← c.comm, sq.w])
  have hj : IsPullback iX j c.i (pullback.fst c.g iY) :=
    IsPullback.of_bot (by dsimp only [j]; rw [pullback.lift_snd, ← c.comm]; exact sq)
      (pullback.lift_fst _ _ _).symm hp
  let cs : Compactification hs :=
    { Z := pullback c.g iY
      g := pullback.snd c.g iY
      i := j
      comm := (pullback.lift_snd _ _ _).symm
      isProper := MorphismProperty.of_isPullback hp inferInstance
      isOpenImmersion := MorphismProperty.of_isPullback hj inferInstance }
  let τ := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) hj.toCommSq
  let Q := τ.isoLocus
  let P := Q.inverseImage (_root_.DerivedCategory.singleFunctor _ 0)
  have hjC : IsIso (τ.app C) := by
    apply _root_.DerivedCategory.prop_of_isGE_of_isLE Q P (fun _ hF ↦ hF)
      (hi - lo + 1).toNat lo C hlo
    · exact _root_.DerivedCategory.TStructure.t.isLE_of_le C hi _ (by omega)
    · intro i hil hih
      have iI : i ∈ I := Finset.mem_Icc.mpr ⟨hil, by omega⟩
      let i' : I := ⟨i, iI⟩
      exact (hBC i' B s (fun x hx ↦ (hmem x).mp (hsW hx) i') _ _ _ _ _ _
        (hp.paste_vert sy) hj).2
  have : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) hp.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite hp
  have key := map_rightDerivedLowerStarCompHom_derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    sq.toCommSq c cs _ hj hp.toCommSq C
  have : IsIso ((upperStar (ModuleCat.{u + 1} Λ) iY).leftDerivedFunctor.map
      ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) c.i c.g h c.comm).app C) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app C) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left ((upperStar (ModuleCat.{u + 1} Λ) iY).leftDerivedFunctor.map
    ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) c.i c.g h c.comm).app C)) _

end WeilII
