module

public import WeilII.AlgebraicGeometry.ShriekExchangeChangePrimedStructure
meta import WeilConjectures.Tactic.ExactByKernel

/-! # The chosen field exchange after changing the primed structure -/

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

/-- For a weakly étale square in one field slice, the chosen slice exchange equals the field
exchange with a second compatible structure on the primed row. Apply the cartesian-pair
formula to the Nagata compactification and its pullback. The middle projection is weakly
étale by base change. These are the compactifications defining the chosen field exchange.
The equality `h` allows the primed arrow to be given by a composite in the slice. After
substituting this equality the two components have the same morphism type. -/
public theorem sliceBaseChange_changePrimedStructure
    {x : Over.mk a ⟶ X} {y : Over.mk b ⟶ Y} {p' : Over.mk a ⟶ Over.mk b} (h : p' = p₁)
    (sq : IsPullback x p' f y)
    [WeaklyEtale y.left]
    (E : boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Q) y.left ≅
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := P) x.left ⋙
        boundedConstructibleLowerShriek ℓ p)
    (hfield : purityFieldLowerShriekBaseChange ℓ f p (πX := x.left) (πY := y.left)
      (by subst p'; exact sq.overLeft) = E)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≍ E.hom.app K := by
  subst p'
  apply heq_of_eq
  let c := compactificationOverField f
  let d := c.ofIsPullback (u := p.left) sq.overLeft
  let r := c.overBaseChangeFst sq
  have hi := c.overBaseChange_isPullback_i sq
  have hp := c.overBaseChange_isPullback_g sq
  have : @WeaklyEtale d.Z c.Z r.left :=
    MorphismProperty.of_isPullback hp.overLeft.flip ‹WeaklyEtale y.left›
  have hE : purityFieldLowerShriekExchange ℓ f p c d (πX := x.left) (πY := y.left) (πZ := r.left)
      hi.overLeft.flip hp.overLeft = E := by
    dsimp only [purityFieldLowerShriekBaseChange, c, d, r,
      Compactification.overBaseChangeFst_left] at hfield ⊢
    exact hfield
  exact_by_kernel (sliceBaseChange_eq_fieldExchange_changeStructure ℓ f p w sq c d r hi hp E hE K)

end WeilII
