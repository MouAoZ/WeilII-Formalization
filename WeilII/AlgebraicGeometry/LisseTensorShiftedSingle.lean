module

public import WeilII.AlgebraicGeometry.IhomLissePrecomp
public import WeilII.HomologicalAlgebra.RightDerivedShiftedSingle
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

attribute [local semireducible] ObjectProperty.hasShift

/-- Tensoring a shifted single Weil sheaf with a lisse coefficient sheaf agrees with
the shifted ordinary tensor product, naturally in the coefficient sheaf. The exact
internal Hom out of the dual computes the derived tensor. Its coefficient map is
precomposition by the dual, both on the complex and on the single sheaf. -/
public theorem lisseTensorShiftedSingle
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (W : WeilSheaf k ℓ X) (s : ℤ) :
    let L := WeilSheaf.toComplex ⋙ shiftFunctor (WeilComplex k ℓ X) s
    ∃ e : ∀ (A : WeilSheaf k ℓ X) (h : A.IsLisse),
      (WeilComplex.tensorLisse A h).obj (L.obj W) ≅ L.obj (A.tensorObj W h),
      ∀ (A B : WeilSheaf k ℓ X) (ha : A.IsLisse) (hb : B.IsLisse) (f : A ⟶ B),
        (ihomLissePrecomp (WeilSheaf.dualMap f ha hb) hb.dual ha.dual).app (L.obj W) ≫
          (e B hb).hom = (e A ha).hom ≫ L.map (WeilSheaf.tensorHom f (𝟙 W) ha hb) := by
  intro L
  obtain ⟨e, he⟩ := rightDerivedShiftedSingle (D := ProEtaleWeilSheaf k ℓ X) W.obj s
  let F (A : WeilSheaf k ℓ X) (h : A.IsLisse) := ProEtaleWeilSheaf.ihomFunctor k ℓ X (A.dual h).obj
  let (A : WeilSheaf k ℓ X) (h : A.IsLisse) : Limits.PreservesFiniteColimits (F A h) :=
    ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor _ h.dual
  refine ⟨fun A h ↦ ObjectProperty.isoMk _ (e (F A h)), ?_⟩
  intro A B ha hb f
  let τ := (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map (WeilSheaf.dualMap f ha hb).hom.op
  have hmap : (WeilSheaf.tensorHom f (𝟙 W) ha hb).hom = τ.app W.obj := by
    change ProEtaleWeilSheaf.ihomMapRight _ (𝟙 _) ≫ _ = _
    erw [ProEtaleWeilSheaf.ihomMapRight_id, Category.id_comp]
    rfl
  apply ObjectProperty.hom_ext
  change _ ≫ _ = _ ≫ (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ s).map
    (WeilSheaf.tensorHom f (𝟙 W) ha hb).hom
  rw [hmap]
  exact he (F A ha) (F B hb) τ

end WeilII
