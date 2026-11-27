module

public import WeilII.AlgebraicGeometry.LisseClosedPullbackCoprojection
public import WeilII.AlgebraicGeometry.LisseTensorRightUnit
public import WeilII.AlgebraicGeometry.LisseTensorShiftedSingle

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Transport a closed-support orientation of the unit to lisse coefficients
(SGA 4, XVI, 3.8). Insert the right tensor unit, move the lisse factor across
closed support, and apply the chosen orientation. Naturality follows by composing
the coefficient squares for these three maps and the shifted single comparison. -/
public theorem lisseClosedPurityOfConstant
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Y ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (W : WeilSheaf k ℓ Y) (s : ℤ) :
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
    let S := WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ) i i.openComplement.ι
      (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
    let P := WeilSheaf.upperStar (k₀ := k) (l := ℓ) i
    let L := WeilSheaf.toComplex ⋙ shiftFunctor (WeilComplex k ℓ Y) s
    Nonempty (S.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k ℓ X)) ≅ L.obj W) →
    ∃ e : ∀ (A : WeilSheaf k ℓ X) (h : A.IsLisse),
      S.obj (WeilSheaf.toComplex.obj A) ≅ L.obj ((P.obj A).tensorObj W (h.upperStar i)),
      ∀ (A B : WeilSheaf k ℓ X) (ha : A.IsLisse) (hb : B.IsLisse) (f : A ⟶ B),
        S.map (WeilSheaf.toComplex.map f) ≫ (e B hb).hom = (e A ha).hom ≫
          L.map (WeilSheaf.tensorHom (P.map f) (𝟙 W) (ha.upperStar i) (hb.upperStar i)) := by
  intro S P L ⟨orientation⟩
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (.of k))
  let one := WeilSheaf.adicConstant k ℓ X
  let single := WeilSheaf.toComplex (k₀ := k) (l := ℓ) (X := X)
  let L₀ := single ⋙ shiftFunctor _ (0 : ℤ)
  let z : single ≅ L₀ := (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (shiftFunctorZero _ ℤ).symm
  obtain ⟨unit, hu⟩ := lisseTensorRightUnit (k := k) (ℓ := ℓ) X
  obtain ⟨e₀, h₀⟩ := lisseTensorShiftedSingle one 0
  obtain ⟨e₁, h₁⟩ := lisseTensorShiftedSingle W s
  obtain ⟨ex, hx⟩ := lisseClosedPullbackCoprojection (k := k) (ℓ := ℓ) i i.openComplement.ι
    (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
  let M := L₀.obj one
  let o : S.obj M ≅ L.obj W := S.mapIso (z.app one).symm ≪≫ orientation
  let source (A : WeilSheaf k ℓ X) (h : A.IsLisse) :=
    z.app A ≪≫ L₀.mapIso (unit A h) ≪≫ (e₀ A h).symm
  refine ⟨fun A h ↦ S.mapIso (source A h) ≪≫ ((ex A h).app M).symm ≪≫
    (WeilComplex.tensorLisse (P.obj A) (h.upperStar i)).mapIso o ≪≫ e₁ _ _, ?_⟩
  intro A B ha hb f
  let q := ihomLissePrecomp (WeilSheaf.dualMap f ha hb) hb.dual ha.dual
  let p := ihomLissePrecomp (WeilSheaf.dualMap (P.map f) (ha.upperStar i) (hb.upperStar i))
    (hb.upperStar i).dual (ha.upperStar i).dual
  have sqz : CommSq (single.map f) (z.app A).hom (z.app B).hom (L₀.map f) :=
    ⟨z.hom.naturality f⟩
  have squ : CommSq f (unit A ha).hom (unit B hb).hom _ := ⟨hu A B ha hb f⟩
  have sq₀ : CommSq (q.app M) (e₀ A ha).hom (e₀ B hb).hom _ := ⟨h₀ A B ha hb f⟩
  have src : CommSq (single.map f) (source A ha).hom (source B hb).hom (q.app M) :=
    sqz.vert_comp ((L₀.map_commSq squ).vert_comp sq₀.vert_inv)
  have sqx : CommSq (p.app (S.obj M)) ((ex A ha).app M).hom ((ex B hb).app M).hom
      (S.map (q.app M)) := ⟨hx A B ha hb f M⟩
  have sqo : CommSq (p.app (S.obj M)) _ _ (p.app (L.obj W)) := ⟨(p.naturality o.hom).symm⟩
  have sq₁ : CommSq (p.app (L.obj W)) (e₁ _ (ha.upperStar i)).hom (e₁ _ (hb.upperStar i)).hom _ :=
    ⟨h₁ _ _ _ _ (P.map f)⟩
  exact ((S.map_commSq src).vert_comp (sqx.vert_inv.vert_comp (sqo.vert_comp sq₁))).w

end WeilII
