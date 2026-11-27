module

public import WeilII.AlgebraicGeometry.CompactificationSliceExchange
import WeilII.AlgebraicGeometry.CompactificationComponentTransport
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The chosen compact-support exchange on a weakly étale square in one field slice -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

/-- Components of the chosen shriek exchange computed with a specified pair of compactifications.
The three factors are the source comparison, the compactification exchange and the target comparison. -/
public theorem fieldShriekExchange_app {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (c : Compactification f.left) (d : Compactification f'.left)
    {x : U'.left ⟶ U.left} {y : V'.left ⟶ V.left} {z : d.Z ⟶ c.Z}
    (hi : IsPullback d.i x z c.i) (hp : IsPullback z d.g c.g y)
    [WeaklyEtale z] [WeaklyEtale y] (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (purityFieldLowerShriekExchange ℓ f f' c d hi hp).hom.app K =
        (boundedConstructibleUpperStarOfMap ℓ (X := V) (Y := V') y).map
          ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (compactificationOverField f) c).hom.app K) ≫
        (purityFieldCompactificationExchange ℓ f f' c d hi hp).hom.app K ≫
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ d
          (compactificationOverField f')).hom.app
            ((boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') x).obj K) := rfl

/-- The bounded compactification exchange restricts its ambient counterpart on a
coefficient object. The two inclusion comparisons have identity components. -/
public theorem fieldCompactificationExchange_component {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (c : Compactification f.left) (d : Compactification f'.left)
    {x : U'.left ⟶ U.left} {y : V'.left ⟶ V.left} {z : d.Z ⟶ c.Z}
    (hi : IsPullback d.i x z c.i) (hp : IsPullback z d.g c.g y)
    [WeaklyEtale z] [WeaklyEtale y] (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((purityFieldCompactificationExchange ℓ f f' c d hi hp).hom.app K).hom =
      (purityFieldCompactificationAmbientExchange ℓ f f' c d hi hp).hom.app K.obj := by
  let P := L((y)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
  let K' := (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') x).obj K
  let b := (purityFieldCompactificationAmbientExchange ℓ f f' c d hi hp).hom.app K.obj
  have hx := congrArg Iso.hom (compactificationCompatibility_component ℓ c K)
  have hy := congrArg Iso.inv (compactificationCompatibility_component ℓ d K')
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).hom.app K = 𝟙 _ at hx
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ d).inv.app K' = 𝟙 _ at hy
  have hx' := (congrArg (fun m ↦ P.map m) hx).trans (P.map_id _)
  refine (purityFieldCompactificationExchange_hom_app_hom ℓ f f' c d hi hp K).trans ?_
  exact (congrArg₂ (· ≫ ·) hx' (congrArg (b ≫ ·) hy)).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The slice exchange can be computed by any cartesian weakly étale pair of
compactifications, using the underlying-scheme exchange between them. Combine the
slice computation with the comparison of the two exchanges on that pair. -/
public theorem sliceBaseChange_eq_fieldExchange {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    (c : Compactification f.left) (d : Compactification f'.left) (r : d.overObj ⟶ c.overObj)
    (hi : IsPullback x d.overI c.overI r) (hp : IsPullback r d.overG c.overG y)
    [@WeaklyEtale d.Z c.Z r.left] [WeaklyEtale y.left] (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K =
      (purityFieldLowerShriekExchange ℓ f f' c d (πZ := r.left) hi.overLeft.flip hp.overLeft).hom.app K := by
  have middle := compactificationSliceExchange_eq_field ℓ c d r hi hp K
  have e := fieldShriekExchange_app ℓ f f' c d (z := r.left) hi.overLeft.flip hp.overLeft K
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq c d r hi hp]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [middle]
  dsimp only [boundedConstructibleUpperStarOfMap, boundedConstructibleUpperStar] at e ⊢
  transport_compactification_component e.symm

end WeilII
