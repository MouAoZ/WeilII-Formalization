module

public import WeilII.AlgebraicGeometry.WeilSheafBaseChangeFieldPullback
import WeilConjectures.WeilSheaf.ArtinSchreierNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- Pullback compatibility for extension of constants, after pullback to a commuting
square of schemes over the extension field. For the coordinate projections in Zhang's
Proposition 1.5, the vertical maps are the coordinate identifications of affine space.
Pull the base-change comparison back along the first vertical map, then identify the
two iterated pullbacks along the equal composites of the square. -/
public theorem weilSheaf_baseChangeField_upperStar_square
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [hK : Fact (ringChar K ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [overY : Y.Over (Spec (CommRingCat.of k))]
    {Z W : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [overW : W.Over (Spec (CommRingCat.of K))]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))]
    (q : Z ⟶ W) [q.IsOver (Spec (CommRingCat.of K))]
    (x : Z ⟶ X.baseChangeField k K) [x.IsOver (Spec (CommRingCat.of K))]
    (y : W ⟶ Y.baseChangeField k K) [y.IsOver (Spec (CommRingCat.of K))]
    (H : WeilSheaf k ℓ Y) (hH : H.IsLisse) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let pK := pullback.map (X ↘ Spec (CommRingCat.of k)) g (Y ↘ Spec (CommRingCat.of k)) g
      p (𝟙 _) (𝟙 _) (by simp) (by simp)
    x ≫ pK = q ≫ y →
      Nonempty ((WeilSheaf.upperStar x).obj ((WeilSheaf.baseChangeField K).obj
        ((WeilSheaf.upperStar p).obj H)) ≅
        (WeilSheaf.upperStar q).obj ((WeilSheaf.upperStar y).obj
          ((WeilSheaf.baseChangeField K).obj H))) := by
  have charProof : hK = (⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩ : Fact (ringChar K ≠ ℓ)) :=
    Subsingleton.elim _ _
  subst hK
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  intro g pK square
  let : pK.IsOver (Spec (CommRingCat.of K)) :=
    ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩
  have lift {v : X.baseChangeField k K ⟶ Y.baseChangeField k K} [v.IsOver (Spec (.of K))]
      {M : WeilSheaf K ℓ (X.baseChangeField k K)} {N : WeilSheaf K ℓ (Y.baseChangeField k K)}
      (c : Nonempty (M ≅ (WeilSheaf.upperStar v).obj N)) (w : x ≫ v = q ≫ y) :
      Nonempty ((WeilSheaf.upperStar x).obj M ≅
        (WeilSheaf.upperStar q).obj ((WeilSheaf.upperStar y).obj N)) := by
    obtain ⟨c⟩ := c
    let a := WeilSheaf.upperStarUpperStarIsoOfComp x v (q ≫ y) w N
    let b := WeilSheaf.upperStarUpperStarIsoOfComp q y (q ≫ y) rfl N
    exact ⟨(WeilSheaf.upperStar x).mapIso c ≪≫ a ≪≫ b.symm⟩
  exact lift (weilSheaf_baseChangeField_upperStar K p H hH) square

end WeilII
