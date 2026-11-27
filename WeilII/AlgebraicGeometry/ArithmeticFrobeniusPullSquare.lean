module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
meta import WeilConjectures.Tactic.ExactByKernel

/-! # The arithmetic pullback exchange in inverse-pushforward coordinates -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII
universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} (p : X ⟶ Y) (h : p ≫ t = s)

private theorem regroup {C : Type*} [Category C] {A B D E F H : C}
    (x : A ≅ B) (g : D ≅ B) (v : D ≅ E) (q : E ≅ F) (y : F ≅ H)
    (a : A ≅ H) (u : E ≅ D) (hu : u = v.symm)
    (ha : a = x ≪≫ g.symm ≪≫ v ≪≫ q ≪≫ y) :
    a = x ≪≫ (q.symm ≪≫ u ≪≫ g).symm ≪≫ y ∧
      a = x ≪≫ (g.symm ≪≫ v ≪≫ q) ≪≫ y := by
  subst a u
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, and_self]

private theorem reverseCongr {S T : Scheme.{u}} {f g : S ⟶ T} (e : f = g) :
    upperStarCongr Λ e.symm = (upperStarCongr Λ e).symm := by cases e; rfl

/-- In pullback coordinates the inverse of the proper square is also the forward
pullback square for extension by zero. The two composition constraints and
the transport along the commutativity equation give the same three factors. -/
theorem arithmeticFrobeniusPullSquare :
    let i := Scheme.Hom.geometricFiberMap p h
    let sq := Scheme.Hom.commSq_geometricGaloisFrobenius p h
    let x := upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso
    let y := upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso
    let ex := Functor.isoWhiskerLeft (upperStar Λ i) x
    let ey := Functor.isoWhiskerRight y (upperStar Λ i)
    let a := upperStarGeometricFiberMapCompFrobeniusIso Λ p h
    a = ex.symm ≪≫ (upperStarSquareComparison Λ sq).symm ≪≫ ey ∧
      a = ex.symm ≪≫ upperStarSquareComparison Λ sq.flip ≪≫ ey := by
  intro i sq x y ex ey a
  let sx := s.geometricGaloisFrobenius.asIso
  let sy := t.geometricGaloisFrobenius.asIso
  have hc := leftMateIso_lowerStarFrobeniusExchange Λ sx sy i
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv p h) sq.w
  have eqn := regroup (Functor.isoWhiskerLeft (upperStar Λ i) x.symm)
    (upperStarComp Λ sx.hom i) (upperStarCongr Λ sq.w) (upperStarComp Λ i sy.hom) ey
    a (upperStarCongr Λ sq.w.symm) (reverseCongr Λ sq.w) hc
  dsimp only [upperStarSquareComparison, ex, ey, CondensedRing.upperStarCongr] at eqn ⊢
  exact_by_kernel eqn

end WeilII
