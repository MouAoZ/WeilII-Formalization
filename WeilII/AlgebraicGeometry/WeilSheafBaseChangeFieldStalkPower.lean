module

public import WeilConjectures.WeilSheaf.BaseChangeField.Stalk

/-!
# Local Frobenius after extension of constants

The finite-field convention in §2 of Zhang, *On an elementary proof of Weil II*, uses this
comparison. The geometric-point argument follows the stalk computation in the pinned
`WeilConjectures.WeilSheaf.BaseChangeField.Stalk`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- At a finite point of a constant field extension the residue cardinality and the local
Frobenius change by the same positive power. For the Frobenius the comparison is equality
of characteristic polynomials. The degree towers give the exponent. Transport the chosen
geometric lift back to the old fiber, and compare it with the chosen lift over its image
by the divisible-degree stalk formula. -/
public theorem weilSheaf_stalk_baseChangeField_power
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] (E : WeilSheaf k ℓ X)
    (y : (X.baseChangeField k K).finitePoints) :
    let a := X ↘ Spec (CommRingCat.of k)
    let b := X.baseChangeField k K ↘ Spec (CommRingCat.of K)
    let π := pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let x : X.finitePoints := ⟨π.base y.1, Scheme.Hom.map_mem_finitePoints π y.2⟩
    let r := Module.finrank k K * b.degreeOver y.1 / a.degreeOver x.1
    0 < r ∧ b.residueCard y.1 = a.residueCard x.1 ^ r ∧
      (((WeilSheaf.baseChangeField K).obj E).stalk y).frobeniusEnd.charpoly =
        ((E.stalk x).frobeniusEnd ^ r).charpoly := by
  intro a b π x r
  let d := Module.finrank k K
  have hd : 0 < d := Module.finrank_pos
  let sq := WeilSheaf.isPullback_baseChangeField (k₀ := k) X K
  have hdvd := Scheme.Hom.degreeOver_dvd_degreeOver_comp π a y.2
  rw [Scheme.Hom.degreeOver_eq_finrank_mul_degreeOver _ _ sq.w.symm y.2] at hdvd
  have hr : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hd
      (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero b y.2))) hdvd)
      (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero a x.2))
  refine ⟨hr, ?_, ?_⟩
  · dsimp only [r, Scheme.Hom.residueCard]
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, pow_mul, ← Module.natCard_eq_pow_finrank]
  · let θ := Scheme.Hom.geometricFiberBaseChangeIso sq
    let hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
      sq d Module.natCard_eq_pow_finrank
    let σ := (algebraicClosureAlgEquiv k K).symm.toAlgHom
    let Θ := specAlgHomAlgebraicClosureIso σ
    let t := b.geometricFiberPointOfFinitePoint y
    let s := Θ.inv ≫ t ≫ θ.inv
    have hsq : Θ.hom ≫ s = t ≫ θ.inv := Iso.hom_inv_id_assoc _ _
    have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow b y
    have hs := WeilSheaf.comp_geometricGaloisFrobenius_pow_mul_of_comp_eq _
      (WeilSheaf.symm_hom_comp_geometricGaloisFrobenius_pow hθ) rfl σ hsq.symm ht
    have hΘ := specGeometricFrobenius_pow_hom_comp_spec_map_algHom σ (b.degreeOver y.1)
    obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_stalkAt_transport hθ hd E Θ hsq hΘ ht hs
    have hproj : θ.inv ≫ a.geometricFiberProj = b.geometricFiberProj ≫ π :=
      Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberProj sq
    have hx := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base a x
    have heq : (a.geometricFiberPointOfFinitePoint x ≫ a.geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k)) =
        (s ≫ a.geometricFiberProj).base (IsLocalRing.closedPoint (AlgebraicClosure k)) := by
      dsimp only [s]
      rw [hx, Category.assoc, Category.assoc, hproj, ← Category.assoc t]
      change π.base y.1 = π.base ((t ≫ b.geometricFiberProj).base
        (Θ.inv.base (IsLocalRing.closedPoint (AlgebraicClosure k))))
      exact congrArg _ ((Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
        b y).symm.trans (congrArg _ (Subsingleton.elim _ _)))
    have hc := E.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ heq (hx ▸ x.2) hdvd
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow a x) hs
    exact e.charpoly_frobeniusEnd.trans hc

end WeilII
