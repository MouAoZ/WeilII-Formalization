module

public import WeilII.Paper.AffineLineExternalTensorPower
public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.WeilSheaf.StalkTensorTrace
import WeilII.AlgebraicGeometry.CoordinateProjectionFieldPoint

/-! # Point trace of an external tensor power

Zhang, *On an elementary proof of Weil II*, equation (2.2.1), p. 3. -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

private theorem trace_pullLisse
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    (E : WeilSheaf k ℓ Y) (hE : E.IsLisse) (m : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k)).fieldPoints (FiniteField.galoisExtension k m)) :
    (affineLineExternalTensorPower.pullLisse f E hE).1.traceFunction m x =
      E.traceFunction m (f.mapFieldPoints _ x) := by
  rw [affineLineExternalTensorPower.pullLisse.eq_def]
  exact WeilSheaf.traceFunction_upperStar f E m x

private theorem trace_coordinateFactor {k : Type u} [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse)
    {n : ℕ} (i : Fin n) (m : ℕ)
    (x : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)).fieldPoints (FiniteField.galoisExtension k m)) :
    (affineLineExternalTensorPower.coordinateFactor E hE i).1.traceFunction m x =
      E.traceFunction m ((AffineSpace.fieldPointsEquiv k _).symm
        (AffineSpace.fieldPointsEquivPi _ k _ x (ULift.up i))) := by
  rw [affineLineExternalTensorPower.coordinateFactor.eq_def]
  let : (AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ ULift.up.{u} i)
    (Spec (CommRingCat.of k))).IsOver (Spec (CommRingCat.of k)) := ⟨AffineSpace.reindex_over _ _⟩
  refine (trace_pullLisse _ _ _ _ _).trans ?_
  apply congrArg (E.traceFunction m)
  exact (AffineSpace.fieldPointsEquiv k _).eq_symm_apply.mpr
    (fieldPointsEquiv_coordinateProjection (ULift.up i) x)

/-- At a field point of positive-dimensional affine space, the trace of the external
power is the product of the traces at its coordinates. Each coordinate projection sends
the affine-line coordinate to the corresponding coordinate function. Apply the pullback
trace formula to every factor, and multiply the traces along the defining tensor fold.
Source: Zhang, equation (2.2.1). -/
public theorem traceFunction_externalTensorPower
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse) {n : ℕ} (hn : 0 < n) (m : ℕ)
    (x : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)).fieldPoints (FiniteField.galoisExtension k m)) :
    let L := FiniteField.galoisExtension k m
    (affineLineExternalTensorPower E hE n).traceFunction m x =
      ∏ i : Fin n, E.traceFunction m ((AffineSpace.fieldPointsEquiv k L).symm
        (AffineSpace.fieldPointsEquivPi _ k L x (ULift.up i))) := by
  intro L
  cases n with
  | zero => omega
  | succ d =>
    let S := Spec (CommRingCat.of k)
    let factor := affineLineExternalTensorPower.coordinateFactor E hE (n := d + 1)
    let t := fun i : Fin (d + 1) ↦ E.traceFunction m ((AffineSpace.fieldPointsEquiv k L).symm
      (AffineSpace.fieldPointsEquivPi _ k L x (ULift.up i)))
    have hf (i : Fin (d + 1)) : (factor i).1.traceFunction m x = t i :=
      trace_coordinateFactor E hE i m x
    have fold (r : ℕ) (idx : Fin r → Fin (d + 1)) :
        (Fin.foldr r (fun i tail ↦ (factor (idx i)).1.tensorObj tail (factor (idx i)).2)
          (factor (Fin.last d)).1).traceFunction m x =
          (∏ j, t (idx j)) * t (Fin.last d) := by
      induction r with
      | zero => simp [Fin.foldr_zero, hf]
      | succ r ih =>
        rw [Fin.foldr_succ, WeilSheaf.traceFunction_tensorObj, ih, hf, Fin.prod_univ_succ]
        ac_rfl
    rw [affineLineExternalTensorPower]
    change _ = ∏ i, t i
    rw [Fin.prod_univ_castSucc]
    exact fold d Fin.castSucc

end WeilII
