module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.Tensor

/-!
# External tensor powers on affine space

Zhang, *On an elementary proof of Weil II*, Proposition 1.5 and Construction 2.5.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

namespace affineLineExternalTensorPower

/-- Pullback with its lissity witness, used for the factors in Zhang's Proposition 1.5.
The witness is given by WeilSheaf.IsLisse.upperStar. -/
@[expose] public noncomputable def pullLisse {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    (E : WeilSheaf k ℓ Y) (hE : E.IsLisse) : {F : WeilSheaf k ℓ X // F.IsLisse} :=
  ⟨(WeilSheaf.upperStar f).obj E, hE.upperStar f⟩

/-- The lisse factor indexed by i in Zhang's Proposition 1.5, pulled back along the projection
that sends the affine-line coordinate to the i-th coordinate function on affine space. -/
@[expose] public noncomputable def coordinateFactor (E : WeilSheaf k ℓ (affineLine k))
    (hE : E.IsLisse) {n : ℕ} (i : Fin n) :
    {F : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) // F.IsLisse} :=
  let proj := AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ ULift.up.{u} i) (Spec (CommRingCat.of k))
  have : proj.IsOver (Spec (CommRingCat.of k)) := ⟨AffineSpace.reindex_over _ _⟩
  pullLisse proj E hE

end affineLineExternalTensorPower

/-- The external tensor power of E in Zhang's Proposition 1.5 and Construction 2.5.
For positive arity, tensor the coordinate pullbacks in increasing order, associating
to the right. The empty product is the constant rank-one Weil sheaf. -/
@[expose] public noncomputable def affineLineExternalTensorPower (E : WeilSheaf k ℓ (affineLine k))
    (hE : E.IsLisse) (n : ℕ) : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) :=
  match n with
  | 0 => WeilSheaf.adicConstant k ℓ _
  | m + 1 =>
    let factor := affineLineExternalTensorPower.coordinateFactor E hE (n := m + 1)
    Fin.foldr m (fun i tail ↦ (factor i.castSucc).1.tensorObj tail (factor i.castSucc).2)
      (factor (Fin.last m)).1

end WeilII
