module

public import WeilII.Paper.AffineLineExternalTensorPower
import WeilII.Paper.PullbackTensorFoldLastFactor
import WeilConjectures.WeilSheaf.ArtinSchreierNormalization
import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# Splitting off the last factor of an external tensor power

Zhang, *On an elementary proof of Weil II*, Proposition 1.5 and the Künneth injection on p. 2.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u


/-- The coefficient comparison for the Künneth injection on p. 2 of Zhang,
*On an elementary proof of Weil II*. For each `r ≥ 1`, on affine `(r + 1)`-space,
pull the coefficient on the first `r` coordinates back along the projection and tensor it
with the last coordinate pullback of `E`. The result is isomorphic to the external power
as a Weil sheaf. For `r = 1` the first projection goes directly to the affine line of `E`.

Proof. In two coordinates the defining right fold is the tensor of the two coordinate
pullbacks, giving the identity isomorphism. For larger powers, let `a` forget the last
coordinate and let `B` be the last coordinate pullback. Composing `a` with the old coordinate
projections gives the corresponding new projections by composition of reindexings. Thus for
each old factor `Fᵢ` and corresponding new factor `Qᵢ` there is a Weil isomorphism
`a⁎Fᵢ ≅ Qᵢ`. Each coordinate factor is lisse by pullback. Induction from the final factor
using lissity of a binary tensor gives lissity of every suffix and of its pullback along `a`.

For each old suffix `T`, compare `a⁎T ⊗ B` with the new suffix starting at the same index.
For a singleton suffix tensor its coordinate comparison with the identity on `B`. For
`T = Fᵢ ⊗ S`, distribute pullback over the tensor and apply the coordinate comparison.
This gives `(Qᵢ ⊗ a⁎S) ⊗ B`. Apply the inverse component at `B.obj` of the iterated
internal-Hom comparison for the duals of the lisse factors `Qᵢ` and `a⁎S`. The component
is a pro-étale Weil isomorphism and lifts to the constructible full subcategory. It gives
`Qᵢ ⊗ (a⁎S ⊗ B)`, to which we apply the suffix isomorphism under tensoring with `Qᵢ`.
Both affine spaces are smooth over the field, hence locally of finite type as required for
the pullback and internal-Hom comparisons. Taking the whole suffix gives the claimed isomorphism. -/
public theorem affineLineExternalTensorPower_lastFactor
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse) :
    (let F := affineLineExternalTensorPower.coordinateFactor E hE (n := 2)
     Nonempty ((F 0).1.tensorObj (F (Fin.last 1)).1 (F 0).2 ≅
       affineLineExternalTensorPower E hE 2)) ∧
    ∀ (r : ℕ), 2 ≤ r →
      let a := AffineSpace.reindex
        (fun i : ULift.{u} (Fin r) ↦ ULift.up.{u} i.down.castSucc) (Spec (CommRingCat.of k))
      let b := AffineSpace.reindex
        (fun _ : PUnit.{u + 1} ↦ ULift.up.{u} (Fin.last r)) (Spec (CommRingCat.of k))
      letI : a.IsOver (Spec (CommRingCat.of k)) := ⟨AffineSpace.reindex_over _ _⟩
      letI : b.IsOver (Spec (CommRingCat.of k)) := ⟨AffineSpace.reindex_over _ _⟩
      let firstFactors := (WeilSheaf.upperStar a).obj (affineLineExternalTensorPower E hE r)
      ∃ h : firstFactors.IsLisse,
        Nonempty (firstFactors.tensorObj ((WeilSheaf.upperStar b).obj E) h ≅
          affineLineExternalTensorPower E hE (r + 1)) := by
  constructor
  · simp only [affineLineExternalTensorPower, Fin.foldr_succ, Fin.foldr_zero, Fin.castSucc_zero]
    exact ⟨Iso.refl _⟩
  rintro (_ | m) hr
  · omega
  intro a b
  -- Use the same over-base witnesses throughout the pullback comparisons.
  generalize (⟨AffineSpace.reindex_over _ _⟩ : a.IsOver (Spec (CommRingCat.of k))) = ha
  generalize (⟨AffineSpace.reindex_over _ _⟩ : b.IsOver (Spec (CommRingCat.of k))) = hb
  intro firstFactors
  let F := affineLineExternalTensorPower.coordinateFactor E hE (n := m + 1)
  let Q := affineLineExternalTensorPower.coordinateFactor E hE (n := m + 1 + 1)
  let coordinateComparison (i : Fin (m + 1)) :
      (WeilSheaf.upperStar a).obj (F i).1 ≅ (Q i.castSucc).1 := by
    let proj {n : ℕ} (i : Fin n) :=
      AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ ULift.up.{u} i) (Spec (.of k))
    have projOver {n : ℕ} (i : Fin n) : (proj i).IsOver (Spec (CommRingCat.of k)) :=
      ⟨AffineSpace.reindex_over _ _⟩
    have factorVal {n : ℕ} (i : Fin n) :
        (affineLineExternalTensorPower.coordinateFactor E hE i).1 =
          (WeilSheaf.upperStar (proj i)).obj E :=
      congrArg Subtype.val ((affineLineExternalTensorPower.coordinateFactor.eq_1 E hE i).trans
        (affineLineExternalTensorPower.pullLisse.eq_1 (proj i) E hE))
    have comp : a ≫ proj i = proj i.castSucc :=
      (AffineSpace.reindex_comp (↾fun _ : PUnit.{u + 1} ↦ ULift.up.{u} i)
        (↾fun j : ULift.{u} (Fin (m + 1)) ↦ ULift.up.{u} j.down.castSucc) (Spec (.of k))).symm
    let pullCoord := WeilSheaf.upperStarUpperStarIsoOfComp a (proj i) (proj i.castSucc) comp E
    exact (WeilSheaf.upperStar a).mapIso (eqToIso (factorVal i)) ≪≫ pullCoord ≪≫
      eqToIso (factorVal i.castSucc).symm
  let B := (Q (Fin.last (m + 1))).1
  let step (i : Fin (m + 1)) t := (Q i.castSucc).1.tensorObj t (Q i.castSucc).2
  let last := (WeilSheaf.upperStar b).obj E
  have hLast : last = B :=
    (congrArg Subtype.val ((affineLineExternalTensorPower.coordinateFactor.eq_1 E hE
      (Fin.last (m + 1))).trans (affineLineExternalTensorPower.pullLisse.eq_1 b E hE))).symm
  let left (i : Fin m) := F i.castSucc
  let right (i : Fin m) := Q i.castSucc.castSucc
  -- Transport at the level of coordinate factors to keep the pullback functor folded.
  have compareFactors (S S' : {T : WeilSheaf k ℓ _ // T.IsLisse})
      (V V' : {T : WeilSheaf k ℓ _ // T.IsLisse}) (hs : S = S') (hv : V = V')
      (c : (WeilSheaf.upperStar a).obj S'.1 ≅ V'.1) :
      (WeilSheaf.upperStar a).obj S.1 ≅ V.1 := hs ▸ hv ▸ c
  let restricted (i : Fin m) : (WeilSheaf.upperStar a).obj (left i).1 ≅ (right i).1 :=
    compareFactors (left i) (F i.castSucc) (right i) (Q i.castSucc.castSucc) rfl rfl
      (coordinateComparison i.castSucc)
  have finish (T T' : WeilSheaf k ℓ _) (Z Z' U U' : WeilSheaf k ℓ _)
      (ht : T = T') (hz : Z = Z') (hu : U = U')
      (fold : ∃ h : T'.IsLisse,
        Nonempty (((WeilSheaf.upperStar a).obj T').tensorObj Z' (h.upperStar a) ≅ U')) :
      ∃ h : ((WeilSheaf.upperStar a).obj T).IsLisse,
        Nonempty (((WeilSheaf.upperStar a).obj T).tensorObj Z h ≅ U) := by
    subst T'
    subst Z'
    subst U'
    obtain ⟨h, e⟩ := fold
    exact ⟨h.upperStar a, e⟩
  refine finish (affineLineExternalTensorPower E hE (m + 1)) _ last B
    (affineLineExternalTensorPower E hE (m + 1 + 1)) _ ?_ hLast ?_
    (pullbackTensorFoldLastFactor a B (F (Fin.last m)) (Q (Fin.last m).castSucc)
      (coordinateComparison (Fin.last m)) m left right restricted)
  · exact affineLineExternalTensorPower.eq_2 E hE m
  · exact (affineLineExternalTensorPower.eq_2 E hE (m + 1)).trans (Fin.foldr_succ_last step B)

end WeilII
