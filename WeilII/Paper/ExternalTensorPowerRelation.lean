module

public import WeilII.Paper.AffineLineExternalTensorPower

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Induction for comparing two positive external tensor powers, possibly over different
constant fields. Start the comparison at the last coordinate, then prepend each earlier
coordinate on both sides. The relation on individual factors can differ from the relation
on suffixes, so the latter can also keep track of lissity. This is the right-associated
product of Zhang, Proposition 1.5. -/
public theorem affineLineExternalTensorPower_relation
    {k K : Type u} [Field k] [Finite k] [Field K] [Finite K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse)
    (G : WeilSheaf K ℓ (affineLine K)) (hG : G.IsLisse) (m : ℕ)
    (S R : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of k)) →
      WeilSheaf K ℓ 𝔸(ULift.{u} (Fin (m + 1)); Spec (.of K)) → Prop)
    (seed : ∀ A C, WeilSheaf.IsLisse A → S A C → R A C)
    (step : ∀ A C (hA : WeilSheaf.IsLisse A) (hC : WeilSheaf.IsLisse C),
      S A C → ∀ T U, R T U → R (A.tensorObj T hA) (C.tensorObj U hC))
    (coords : ∀ i : Fin (m + 1), S (affineLineExternalTensorPower.coordinateFactor E hE i).1
      (affineLineExternalTensorPower.coordinateFactor G hG i).1) :
    R (affineLineExternalTensorPower E hE (m + 1)) (affineLineExternalTensorPower G hG (m + 1)) := by
  let F := affineLineExternalTensorPower.coordinateFactor E hE (n := m + 1)
  let Q := affineLineExternalTensorPower.coordinateFactor G hG (n := m + 1)
  have fold (r : ℕ) (idx : Fin r → Fin (m + 1)) :
      R (Fin.foldr r (fun i t ↦ (F (idx i)).1.tensorObj t (F (idx i)).2) (F (Fin.last m)).1)
        (Fin.foldr r (fun i t ↦ (Q (idx i)).1.tensorObj t (Q (idx i)).2) (Q (Fin.last m)).1) := by
    induction r with
    | zero =>
      rw [Fin.foldr_zero, Fin.foldr_zero]
      exact seed _ _ (F (Fin.last m)).2 (coords (Fin.last m))
    | succ r ih =>
      rw [Fin.foldr_succ, Fin.foldr_succ]
      exact step _ _ (F (idx 0)).2 (Q (idx 0)).2 (coords (idx 0)) _ _ (ih (fun i ↦ idx i.succ))
  rw [affineLineExternalTensorPower.eq_2 E hE, affineLineExternalTensorPower.eq_2 G hG]
  exact fold m Fin.castSucc

end WeilII
