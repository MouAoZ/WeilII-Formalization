module

public import WeilConjectures.WeilSheaf.ArtinSchreierNormalization
import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# Pullback of a right-associated tensor product with one further factor
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- Pull back the right fold of a family of lisse Weil sheaves and tensor it with one
more factor. Coordinatewise pullback isomorphisms identify the result with the extended
right fold. The initial factor of each fold is supplied separately.

This is the coefficient comparison used for Zhang, Proposition 1.5 and the Künneth
injection on page 2. Start with the given isomorphism of the initial factors tensored
with the identity on the last factor. For each preceding factor, distribute pullback over
tensor product, transport the factor isomorphism, and reassociate using composition of
internal Hom out of the lisse duals. Lissity of the old suffix is preserved by tensoring. -/
public theorem pullbackTensorFoldLastFactor {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))] (a : X ⟶ Y)
    [a.IsOver (Spec (CommRingCat.of k))] (B : WeilSheaf k ℓ X)
    (L : {T : WeilSheaf k ℓ Y // T.IsLisse}) (M : {T : WeilSheaf k ℓ X // T.IsLisse})
    (cL : (WeilSheaf.upperStar a).obj L.1 ≅ M.1) (s : ℕ)
    (F : Fin s → {T : WeilSheaf k ℓ Y // T.IsLisse})
    (Q : Fin s → {T : WeilSheaf k ℓ X // T.IsLisse})
    (c : ∀ i, (WeilSheaf.upperStar a).obj (F i).1 ≅ (Q i).1) :
    let T := Fin.foldr s (fun i t ↦ (F i).1.tensorObj t (F i).2) L.1
    let U := Fin.foldr s (fun i t ↦ (Q i).1.tensorObj t (Q i).2) (M.1.tensorObj B M.2)
    ∃ h : T.IsLisse, Nonempty (((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U) := by
  let R (T : WeilSheaf k ℓ Y) (U : WeilSheaf k ℓ X) :=
    ∃ h : T.IsLisse, Nonempty (((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U)
  have pack (T : WeilSheaf k ℓ Y) (U : WeilSheaf k ℓ X) (h : T.IsLisse)
      (e : ((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U) : R T U :=
    ⟨h, ⟨e⟩⟩
  have unpack (T : WeilSheaf k ℓ Y) (U : WeilSheaf k ℓ X) (hr : R T U) :
      ∃ h : T.IsLisse, Nonempty (((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U) :=
    hr
  have liftFold (P : WeilSheaf k ℓ Y → WeilSheaf k ℓ X → Prop)
      (put : ∀ (T : WeilSheaf k ℓ Y) (U : WeilSheaf k ℓ X) (h : T.IsLisse),
        (((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U) → P T U)
      (get : ∀ T U, P T U → ∃ h : T.IsLisse,
        Nonempty (((WeilSheaf.upperStar a).obj T).tensorObj B (h.upperStar a) ≅ U)) :
      P (Fin.foldr s (fun i t ↦ (F i).1.tensorObj t (F i).2) L.1)
        (Fin.foldr s (fun i t ↦ (Q i).1.tensorObj t (Q i).2) (M.1.tensorObj B M.2)) := by
    let tensorAsFunctor (A Z : WeilSheaf k ℓ X) (hA : A.IsLisse) : (A.tensorObj Z hA).obj =
        (ProEtaleWeilSheaf.ihomFunctor k ℓ X (A.dual hA).obj).obj Z.obj :=
      (WeilSheaf.tensorObj_obj A Z hA).trans (ProEtaleWeilSheaf.ihomFunctor_obj _ _).symm
    have prepend (A : WeilSheaf k ℓ Y) (C : WeilSheaf k ℓ X) (hA : A.IsLisse) (hC : C.IsLisse)
        (eA : (WeilSheaf.upperStar a).obj A ≅ C) {T U} (ih : P T U) :
        P (A.tensorObj T hA) (C.tensorObj U hC) := by
      obtain ⟨hT, ⟨e⟩⟩ := get T U ih
      let D := (WeilSheaf.upperStar a).obj T
      let hD := hT.upperStar a
      let dist := WeilSheaf.upperStarTensorObjIso a A T hA ≪≫
        WeilSheaf.tensorObjIsoOfIso eA (Iso.refl D) (hA.upperStar a) hC
      let assoc : (C.tensorObj D hC).tensorObj B (hC.tensorObj hD) ≅
          C.tensorObj (D.tensorObj B hD) hC :=
        ObjectProperty.isoMk _ (eqToIso (tensorAsFunctor (C.tensorObj D hC) B (hC.tensorObj hD)) ≪≫
          ((ProEtaleWeilSheaf.ihomFunctorDualCompIhomFunctorDualIso C D hC hD).app B.obj).symm ≪≫
          eqToIso ((congrArg (ProEtaleWeilSheaf.ihomFunctor k ℓ X (C.dual hC).obj).obj
            (tensorAsFunctor D B hD).symm).trans (tensorAsFunctor C (D.tensorObj B hD) hC).symm))
      let left := WeilSheaf.tensorObjIsoOfIso dist (Iso.refl B) ((hA.tensorObj hT).upperStar a)
        (hC.tensorObj hD)
      let right := WeilSheaf.tensorObjIsoOfIso (Iso.refl C) e hC hC
      exact put (A.tensorObj T hA) (C.tensorObj U hC) (hA.tensorObj hT) (left ≪≫ assoc ≪≫ right)
    have foldRel {A C : Type _} (P : A → C → Prop) (x : A) (y : C) (h : P x y)
        (s : ℕ) (f : Fin s → A → A) (g : Fin s → C → C)
        (step : ∀ i t u, P t u → P (f i t) (g i u)) :
        P (Fin.foldr s f x) (Fin.foldr s g y) := by
      induction s with
      | zero => simpa only [Fin.foldr_zero] using h
      | succ s ih =>
        rw [Fin.foldr_succ, Fin.foldr_succ]
        exact step 0 _ _ (ih (fun j ↦ f j.succ) (fun j ↦ g j.succ) (fun j ↦ step j.succ))
    have base : P L.1 (M.1.tensorObj B M.2) :=
      put L.1 (M.1.tensorObj B M.2) L.2 (WeilSheaf.tensorObjIsoOfIso cL (Iso.refl B) (L.2.upperStar a) M.2)
    exact foldRel P L.1 (M.1.tensorObj B M.2) base s
      (fun i t ↦ (F i).1.tensorObj t (F i).2) (fun i t ↦ (Q i).1.tensorObj t (Q i).2)
      (fun i t v ↦ @prepend (F i).1 (Q i).1 (F i).2 (Q i).2 (c i) t v)
  exact unpack _ _ (liftFold R pack unpack)
end WeilII
