module

public import WeilII.Paper.AffineLineExternalTensorPower
import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# Lissity of the geometric external tensor power

Zhang, *On an elementary proof of Weil II*, Construction 2.5, applies Theorem 2.4 to the
external tensor power of Proposition 1.5 over an algebraic closure of the base field.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The geometric external tensor power in Zhang's Construction 2.5 is lisse on affine space
over any algebraic closure `K` of the finite base field `k`.

Proof. Each coordinate projection is a morphism over `k`, so pulling back `hE` along it
gives a lissity witness for the corresponding factor. Since `n ≥ 2`, there is a last factor.
Start with its witness and proceed backwards through the preceding coordinates. At each step
`WeilSheaf.IsLisse.tensorObj` combines the coordinate witness with the witness for the tail.
This proves lissity of the right-associated external tensor power. By definition this is
lissity of its carrier on the geometric fiber. The affine-space base-change square identifies
affine space over `AlgebraicClosure k` with that fiber. The field isomorphism `e` identifies
affine space over `K` with the former affine space. Pulling the carrier back along the
composite preserves lissity by `ProEtale.IsAdicLisseSheaf.upperStar`. -/
public theorem geometricExternalTensorPowerLisse {k : Type u} [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (E : WeilSheaf k ℓ (affineLine k))
    (hE : E.IsLisse) (n : ℕ) (hn : 2 ≤ n) (K : Type u) [Field K] [Algebra k K]
    [IsAlgClosure k K] (e : AlgebraicClosure k ≃ₐ[k] K := IsAlgClosure.equiv k _ _) :
    let I := ULift.{u} (Fin n)
    let toClosure := AffineSpace.map I (Spec.map (CommRingCat.ofHom e.toRingHom))
    let toFiber :=
      (AffineSpace.isPullback_map (n := I) (Scheme.specAlgebraicClosure k).hom).isoPullback
    ProEtale.IsAdicLisseSheaf ((ProEtale.adicUpperStar ℓ (toClosure ≫ toFiber.hom)).obj
      (affineLineExternalTensorPower E hE n).carrier) := by
  apply ProEtale.IsAdicLisseSheaf.upperStar
  change (affineLineExternalTensorPower E hE n).IsLisse
  cases n with
  | zero => exact (Nat.not_succ_le_zero 1 hn).elim
  | succ m =>
    let F := affineLineExternalTensorPower.coordinateFactor E hE (n := m + 1)
    suffices ∀ (r : ℕ) (idx : Fin r → Fin (m + 1)),
        (Fin.foldr r (fun i tail ↦ (F (idx i)).1.tensorObj tail (F (idx i)).2)
          (F (Fin.last m)).1).IsLisse from
      this m Fin.castSucc
    intro r
    induction r with
    | zero =>
      intro idx
      rw [Fin.foldr_zero]
      exact (F (Fin.last m)).2
    | succ r ih =>
      intro idx
      rw [Fin.foldr_succ]
      exact (F (idx 0)).2.tensorObj (ih (fun i ↦ idx i.succ))

end WeilII
