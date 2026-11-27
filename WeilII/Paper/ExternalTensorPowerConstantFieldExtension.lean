module

public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
import WeilConjectures.WeilSheaf.ArtinSchreierNormalization
import WeilConjectures.WeilSheaf.StalkTensorTrace
import WeilII.AlgebraicGeometry.WeilSheafConstantExtensionPullbackSquare
import WeilII.AlgebraicGeometry.WeilSheafConstantExtensionTensorPullback
import WeilII.Paper.ExternalTensorPowerRelation

/-!
# External tensor powers after a finite extension of constants

Zhang, *On an elementary proof of Weil II*, p. 2 (finite field extensions) and
pp. 3–4 (Construction 2.5 and the proof of Proposition 1.5).
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The coordinate identification for the change of constants on p. 2 of Zhang.
The cartesian square for relative affine space gives an isomorphism from affine space
over the new field to the fiber product over the original field. -/
@[expose] public noncomputable def affineSpaceBaseChangeFieldIso (k K : Type u)
    [Field k] [Field K] [Algebra k K] (I : Type u) :
    𝔸(I; Spec (CommRingCat.of K)) ≅ (𝔸(I; Spec (CommRingCat.of k))).baseChangeField k K :=
  (AffineSpace.isPullback_map (n := I) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isoPullback

/-- The identification used in Zhang's change of constants is over the extension field,
since its composite with the second pullback projection is the structure map. -/
public instance affineSpaceBaseChangeFieldIso_isOver (k K : Type u) [Field k] [Field K]
    [Algebra k K] (I : Type u) :
    (affineSpaceBaseChangeFieldIso k K I).hom.IsOver (Spec (CommRingCat.of K)) :=
  ⟨(AffineSpace.isPullback_map (n := I)
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isoPullback_hom_snd⟩

section BaseChange

variable {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)] {I : Type u}

/-- Extension of the constants of a Weil sheaf on affine space, placed in the coordinates
used in Zhang's Construction 2.5 by pullback along the cartesian identification. -/
@[expose] public noncomputable def affineSpaceWeilSheafBaseChangeField
    (F : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))) :
    WeilSheaf K ℓ 𝔸(I; Spec (CommRingCat.of K)) :=
  (WeilSheaf.upperStar (affineSpaceBaseChangeFieldIso k K I).hom).obj
    ((WeilSheaf.baseChangeField K).obj F)

/-- The extended sheaf used in Zhang's Construction 2.5 is lisse: restriction to the
fiber product preserves lissity, as does pullback along the coordinate identification. -/
public theorem isLisse_affineSpaceWeilSheafBaseChangeField
    {F : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))} (hF : F.IsLisse) :
    (affineSpaceWeilSheafBaseChangeField K F).IsLisse :=
  (hF.baseChangeField K).upperStar (affineSpaceBaseChangeFieldIso k K I).hom

end BaseChange

/-- The external tensor power in Zhang's Proposition 1.5 (p. 1) commutes with the finite
field extension used in Construction 2.5 (pp. 2–4).

Write R for restriction to the fiber product and e for its coordinate identification.
On geometric sheaves R transports the old Weil structure iterated [K : k] times.
Each coordinate projection commutes with the affine-space base-change map. Thus restriction
of its pullback, followed by pullback along e, is isomorphic to the coordinate pullback of
the extended sheaf. These are Weil isomorphisms by compatibility of the geometric pullback
square with each iterate of Frobenius.

Induct from the last coordinate towards the first in the right-associated tensor. The last
factor has the coordinate isomorphism just described. At each preceding factor apply the
binary tensor comparison first for R and then for pullback along e. Both factors are lisse
by pullback and tensor stability. The tensor comparison respects the iterated Weil structure
because tensoring the two structure maps commutes with their successive compositions.
Tensor the coordinate isomorphism with the induction isomorphism for the suffix.
The resulting isomorphism at the first factor is the required one on affine space over K. -/
public theorem affineLineExternalTensorPower_baseChangeField
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse) (n : ℕ) (_hn : 2 ≤ n) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    Nonempty (affineSpaceWeilSheafBaseChangeField K (affineLineExternalTensorPower E hE n) ≅
      affineLineExternalTensorPower (affineSpaceWeilSheafBaseChangeField K E)
        (isLisse_affineSpaceWeilSheafBaseChangeField K hE) n) := by
  classical
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst n
  suffices ∀ (EK : WeilSheaf K ℓ (affineLine K)) (hEK : EK.IsLisse),
      EK = affineSpaceWeilSheafBaseChangeField K E →
      Nonempty (affineSpaceWeilSheafBaseChangeField K (affineLineExternalTensorPower E hE (m + 1)) ≅
        affineLineExternalTensorPower EK hEK (m + 1)) from
    this _ (isLisse_affineSpaceWeilSheafBaseChangeField K hE) rfl
  intro EK hEK hLine
  suffices ∀ (extend : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of k)) →
      WeilSheaf K ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of K))),
      (∀ A, extend A = affineSpaceWeilSheafBaseChangeField K A) →
      Nonempty (extend (affineLineExternalTensorPower E hE (m + 1)) ≅
        affineLineExternalTensorPower EK hEK (m + 1)) from
    this (affineSpaceWeilSheafBaseChangeField K) (fun _ ↦ rfl)
  intro extend hExtend
  let B (A C) := Nonempty (extend A ≅ C)
  have inCoords (A C) : B A C ↔
      Nonempty ((WeilSheaf.upperStar (affineSpaceBaseChangeFieldIso k K (ULift.{u} (Fin (m + 1)))).hom).obj
        ((WeilSheaf.baseChangeField K).obj A) ≅ C) := by
    have h := (hExtend A).trans (affineSpaceWeilSheafBaseChangeField.eq_def K A)
    exact Iff.of_eq (congrArg (fun V ↦ Nonempty (V ≅ C)) h)
  have transport {A A' C C'}
      (ha : A = A') (hc : C = C') (h : B A' C') : B A C := ha ▸ hc ▸ h
  have coord (i : Fin (m + 1)) :
      B (affineLineExternalTensorPower.coordinateFactor E hE i).1
        (affineLineExternalTensorPower.coordinateFactor EK hEK i).1 := by
    let idx := fun _ : PUnit.{u + 1} ↦ ULift.up.{u} i
    let p := AffineSpace.reindex idx (Spec (CommRingCat.of k))
    let q := AffineSpace.reindex idx (Spec (CommRingCat.of K))
    have : p.IsOver (Spec (CommRingCat.of k)) := ⟨AffineSpace.reindex_over _ _⟩
    have : q.IsOver (Spec (CommRingCat.of K)) := ⟨AffineSpace.reindex_over _ _⟩
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let J := ULift.{u} (Fin (m + 1))
    let X := 𝔸(J; Spec (.of k))
    let Z := 𝔸(J; Spec (.of K))
    let e := affineSpaceBaseChangeFieldIso k K J
    let e₁ := affineSpaceBaseChangeFieldIso k K PUnit.{u + 1}
    let pK := Limits.pullback.map (X ↘ Spec (CommRingCat.of k)) g
      (affineLine k ↘ Spec (CommRingCat.of k)) g p (𝟙 _) (𝟙 _) (by simp) (by simp)
    have square : e.hom ≫ pK = q ≫ e₁.hom := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, show pK ≫ _ = Limits.pullback.fst (X ↘ _) g ≫ p from
            Limits.pullback.lift_fst _ _ _, ← Category.assoc,
          show e.hom ≫ Limits.pullback.fst (X ↘ _) g = AffineSpace.map J g from
            (AffineSpace.isPullback_map g).isoPullback_hom_fst,
          Category.assoc, show e₁.hom ≫ Limits.pullback.fst (affineLine k ↘ _) g = _ from
            (AffineSpace.isPullback_map (n := PUnit.{u + 1}) g).isoPullback_hom_fst]
        exact AffineSpace.map_reindex idx g
      · rw [Category.assoc, show pK ≫ _ = Limits.pullback.snd (X ↘ _) g from
            (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _),
          show e.hom ≫ Limits.pullback.snd (X ↘ _) g = Z ↘ _ from
            (AffineSpace.isPullback_map (n := J) g).isoPullback_hom_snd,
          Category.assoc, show e₁.hom ≫ Limits.pullback.snd (affineLine k ↘ _) g = _ from
            (AffineSpace.isPullback_map (n := PUnit.{u + 1}) g).isoPullback_hom_snd]
        exact (AffineSpace.reindex_over idx _).symm
    -- Write the line as one-coordinate affine space on both sides of the pullback.
    have rawFactor {L : Type u} [Field L] [Finite L] [Fact (ringChar L ≠ ℓ)]
        (pL : 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of L)) ⟶ 𝔸(PUnit.{u + 1}; Spec (.of L)))
        [Scheme.Hom.IsOver pL (Spec (.of L))] (hpL : pL = AffineSpace.reindex idx (Spec (.of L)))
        (F G : WeilSheaf L ℓ 𝔸(PUnit.{u + 1}; Spec (.of L))) (hF : F.IsLisse) (h : F = G) :
        (affineLineExternalTensorPower.coordinateFactor F hF i).1 = (WeilSheaf.upperStar pL).obj G := by
      subst G
      subst pL
      exact congrArg Subtype.val ((affineLineExternalTensorPower.coordinateFactor.eq_1 F hF i).trans
        (affineLineExternalTensorPower.pullLisse.eq_1 (AffineSpace.reindex idx (Spec (.of L))) F hF))
    have extended : EK =
        (WeilSheaf.upperStar (affineSpaceBaseChangeFieldIso k K PUnit.{u + 1}).hom).obj
          ((WeilSheaf.baseChangeField K).obj E) :=
      hLine.trans (affineSpaceWeilSheafBaseChangeField.eq_def K E)
    have hf := rawFactor p rfl E E hE rfl
    have target := rawFactor q rfl EK _ hEK extended
    with_reducible
      have c := weilSheaf_baseChangeField_upperStar_square K p q
        (affineSpaceBaseChangeFieldIso k K (ULift.{u} (Fin (m + 1)))).hom
        (affineSpaceBaseChangeFieldIso k K PUnit.{u + 1}).hom E hE square
      have converted := (inCoords _ _).mpr c
      exact transport hf target converted
  -- Compare the two folds while retaining the lissity of the original suffix.
  let P (T : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of k))) (U) :=
    T.IsLisse ∧ B T U
  have pack (A : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of k))) (C)
      (hA : A.IsLisse) (h : B A C) : P A C := ⟨hA, h⟩
  have prepend (A : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of k)))
      (C : WeilSheaf K ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of K)))
      (hA : A.IsLisse) (hC : C.IsLisse) (first : B A C) (T U) (tail : P T U) :
      P (A.tensorObj T hA) (C.tensorObj U hC) := by
    obtain ⟨hT, second⟩ := tail
    with_reducible
      have paired := weilSheaf_baseChangeField_tensorObj_pullback K
        (affineSpaceBaseChangeFieldIso k K (ULift.{u} (Fin (m + 1)))).hom A T hA hT C U hC
        ((inCoords A C).mp first) ((inCoords T U).mp second)
      exact pack _ _ (hA.tensorObj hT) ((inCoords _ _).mpr paired)
  have folded := affineLineExternalTensorPower_relation E hE EK hEK m B P pack prepend coord
  exact folded.2

end WeilII
