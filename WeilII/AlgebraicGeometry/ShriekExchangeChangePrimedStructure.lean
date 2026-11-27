module

public import WeilII.AlgebraicGeometry.CompactificationSliceExchange
import WeilII.AlgebraicGeometry.CompactificationComparisonNatIso
meta import WeilConjectures.Tactic.RflByKernel
meta import WeilConjectures.Tactic.ExactByKernel

/-! # Computing field exchange on a cartesian pair in a second primed field structure -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y P Q : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    (f : X ⟶ Y) (p : P ⟶ Q)
    {a : P.left ⟶ Spec (.of k)} {b : Q.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    (w : p.left ≫ b = a)

local notation "p₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) p.left w

/-- Compute the exchange on a cartesian compactification pair in a common slice even if
the specified field exchange uses a different compatible structure on the primed row.
The slice formula supplies three factors. The first comparison belongs to the unprimed row.
The compactification exchange in the middle restricts the ambient scheme exchange, and its
inclusion comparisons depend only on the underlying arrows. The last comparison is invariant
as a natural isomorphism by computing it on the same two proper refinements. -/
public theorem sliceBaseChange_eq_fieldExchange_changeStructure
    {x : Over.mk a ⟶ X} {y : Over.mk b ⟶ Y} (sq : IsPullback x p₁ f y)
    (c : Compactification f.left) (d : Compactification p.left)
    (r : d.overObj (f := p₁) ⟶ c.overObj (f := f))
    (hi : IsPullback x (d.overI (f := p₁)) (c.overI (f := f)) r)
    (hp : IsPullback r (d.overG (f := p₁)) (c.overG (f := f)) y)
    [@WeaklyEtale d.Z c.Z r.left] [WeaklyEtale y.left]
    (E : boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Q) y.left ≅
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := P) x.left ⋙
        boundedConstructibleLowerShriek ℓ p)
    (hE : purityFieldLowerShriekExchange ℓ f p c d (πX := x.left) (πY := y.left) (πZ := r.left)
      hi.overLeft.flip hp.overLeft = E)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K = E.hom.app K := by
  subst E
  have mid := compactificationSliceExchange_eq_field ℓ (f := f) (f' := p₁) c d r hi hp K
  have fin := compactificationComparisonIso_changeStructure ℓ p w d (compactificationOverField p)
  have middle :
      purityFieldCompactificationExchange ℓ f p₁ c d (πZ := r.left) hi.overLeft.flip hp.overLeft =
      purityFieldCompactificationExchange ℓ f p c d (πZ := r.left) hi.overLeft.flip hp.overLeft := by
    dsimp only [purityFieldCompactificationExchange, purityFieldCompactificationAmbientExchange,
      boundedConstructibleLowerShriekOfCompactificationCompatibility, Over.homMk_left, Over.mk_left]
    rfl_by_kernel
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq c d r hi hp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mid, middle]
  let K' := (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := P) x.left).obj K
  let first := (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Q) y.left).map
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (f := f) (compactificationOverField f) c).hom.app K)
  let exchange := (purityFieldCompactificationExchange ℓ f p c d (πZ := r.left)
    hi.overLeft.flip hp.overLeft).hom.app K
  let J := boundedConstructibleLowerShriekOfCompactification ℓ (f := p) d
  let paste (i : J ≅ boundedConstructibleLowerShriek ℓ p) := first ≫ exchange ≫ i.hom.app K'
  let i₁ : J ≅ boundedConstructibleLowerShriek ℓ p := by
    exact_by_kernel (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := p₁) d
      (compactificationOverField p₁))
  let i₀ := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := p) d
    (compactificationOverField p)
  have hi' : i₁ = i₀ := by exact_by_kernel fin
  exact_by_kernel (congrArg paste hi')

end WeilII
