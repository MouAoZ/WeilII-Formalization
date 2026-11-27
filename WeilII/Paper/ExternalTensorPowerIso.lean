module

public import WeilII.Paper.AffineLineExternalTensorPower
import WeilConjectures.WeilSheaf.ArtinSchreierNormalization

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

private noncomputable def pullLisseIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] {E F : WeilSheaf k ℓ Y}
    (e : E ≅ F) (hE : E.IsLisse) (hF : F.IsLisse) :
    (affineLineExternalTensorPower.pullLisse f E hE).1 ≅
      (affineLineExternalTensorPower.pullLisse f F hF).1 := by
  rw [affineLineExternalTensorPower.pullLisse.eq_def, affineLineExternalTensorPower.pullLisse.eq_def]
  exact (WeilSheaf.upperStar f).mapIso e

private theorem coordNonempty
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {E F : WeilSheaf k ℓ (affineLine k)} (e : E ≅ F)
    (hE : E.IsLisse) (hF : F.IsLisse) {n : ℕ} (i : Fin n) :
    Nonempty ((affineLineExternalTensorPower.coordinateFactor E hE i).1 ≅
    (affineLineExternalTensorPower.coordinateFactor F hF i).1) := by
  let S := Spec (CommRingCat.of k)
  let p := AffineSpace.reindex (fun _ : PUnit.{u+1} ↦ ULift.up.{u} i) S
  let : p.IsOver S := ⟨AffineSpace.reindex_over _ _⟩
  exact ⟨pullLisseIso (X := 𝔸(ULift.{u} (Fin n); S)) (Y := 𝔸(PUnit.{u+1}; S)) p e hE hF⟩

private theorem foldIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] {I : Type*}
    (A B : I → {V : WeilSheaf k ℓ X // V.IsLisse})
    (coord : ∀ i, Nonempty ((A i).1 ≅ (B i).1)) (last : I) (r : ℕ) (idx : Fin r → I) :
    Nonempty (Fin.foldr r (fun j tail ↦ (A (idx j)).1.tensorObj tail (A (idx j)).2) (A last).1 ≅
      Fin.foldr r (fun j tail ↦ (B (idx j)).1.tensorObj tail (B (idx j)).2) (B last).1) := by
  induction r with
  | zero => simpa only [Fin.foldr_zero] using coord last
  | succ r ih =>
    rw [Fin.foldr_succ, Fin.foldr_succ]
    obtain ⟨first⟩ := coord (idx 0)
    obtain ⟨tail⟩ := ih (fun j ↦ idx j.succ)
    exact ⟨WeilSheaf.tensorObjIsoOfIso first tail _ _⟩

/-- The coordinate external tensor power carries a Weil isomorphism of lisse coefficients
to an isomorphism, as used when identifying the coefficients after a change of field
in Zhang, §2. Pull back the isomorphism on every coordinate and tensor the resulting
maps along the defining fold. The empty tensor is the unit on both sides. -/
public theorem affineLineExternalTensorPower_isoOfIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {E F : WeilSheaf k ℓ (affineLine k)} (e : E ≅ F)
    (hE : E.IsLisse) (hF : F.IsLisse) (n : ℕ) :
    Nonempty (affineLineExternalTensorPower E hE n ≅ affineLineExternalTensorPower F hF n) := by
  cases n with
  | zero => simp only [affineLineExternalTensorPower]; exact ⟨Iso.refl _⟩
  | succ m =>
    simp only [affineLineExternalTensorPower]
    exact foldIso (X := 𝔸(ULift.{u} (Fin (m+1)); Spec (CommRingCat.of k)))
      (affineLineExternalTensorPower.coordinateFactor E hE)
      (affineLineExternalTensorPower.coordinateFactor F hF)
      (coordNonempty e hE hF) (Fin.last m) m Fin.castSucc

end WeilII
