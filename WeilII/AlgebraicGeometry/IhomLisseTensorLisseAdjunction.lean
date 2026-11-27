module

public import WeilII.AlgebraicGeometry.IhomLissePrecomp
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilII.AlgebraicGeometry.ProEtaleWeilLisseDualTensorEvaluation
import WeilII.CategoryTheory.ExactRightDerivedAdjunction
import WeilConjectures.CategoryTheory.Adjunction.ConjugateHomEquiv
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# The internal Hom and tensor adjunction for lisse Weil coefficients

The ordinary adjunction is from `WeilConjectures.WeilSheaf.TensorHomAdjunction`. Its
coefficient action is given by `ProEtaleWeilSheaf.nativeTensorMap`. We use the derived
functors on bounded constructible Weil complexes from `WeilConjectures.WeilSheaf.Fourier`.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The adjunctions `R𝓗om(A, −) ⊣ A ⊗ −` can be chosen simultaneously so that precomposition
by every lisse coefficient morphism transposes to precomposition by its dual.

On all pro-étale Weil sheaves, write `F_A = [A, −]` and `G_A = [Aᵛ, −]`. The dual tensor
evaluation identifies `− ⊗ Aᵛ` with `F_A`. Compose this identification with the ordinary
tensor–Hom adjunction at `Aᵛ` to obtain `F_A ⊣ G_A`. For a coefficient map `f : A ⟶ A'`,
write `s : F_A' ⟶ F_A` and `t : G_A ⟶ G_A'` for precomposition by `f` and its dual.
Naturality of evaluation identifies `s` with tensoring by the dual map. The latter is the
inverse transpose of `t` by the definition of `ProEtaleWeilSheaf.nativeTensorMap`. Applying
this transpose formula to the identity of `F_A B` gives the unit equation
`η_A'(B) ≫ G_A'(s_B) = η_A(B) ≫ t_(F_A B)`.

Both coefficients are lisse, so their internal Hom functors preserve finite colimits
(`ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor`) and finite limits. Their additive
adjunction extends degreewise to complexes and preserves the unit equation in each degree.
Exactness makes both functors preserve quasi-isomorphisms. Localize the adjunction using
`Adjunction.localization` and identify the resulting functors with the total right derived
functors by the exact-functor comparison. At the localization of a complex the derived unit
is the image of the degreewise unit under these comparisons. The defining square of
`Functor.rightDerivedFunctorNatTrans` identifies the images of `s` and `t` with the derived
coefficient maps under the same comparisons. Thus applying localization to the unit equation
gives the derived unit equation there, and naturality transports it to every derived object.
For an arbitrary derived arrow `x`, the transpose of `s_B ≫ x` is
`η_A'(B) ≫ G_A'(s_B) ≫ G_A'(x)`. Substituting the unit equation and using naturality of
`t` at `x` gives the transpose of `x` followed by `t_N`.

Finally both functors preserve bounded constructible objects by
`WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor`. Restrict the adjunction to
this full subcategory. The Hom sets and the coefficient arrows are the underlying ones,
and `WeilComplex.tensorLisse` is the restricted derived internal Hom out of the dual.

Sources: `WeilConjectures.WeilSheaf.TensorHomAdjunction`,
`WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations`, and
`WeilConjectures.WeilSheaf.Fourier` at revision 497f33d964609973fe4ed9647a1e5d32369f0d09. -/
public theorem exists_ihomLisse_tensorLisse_adjunction
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    ∃ adj : ∀ (A : WeilSheaf k ℓ X) (hA : A.IsLisse),
        WeilComplex.ihomLisse A hA ⊣ WeilComplex.tensorLisse A hA,
      ∀ (A A' : WeilSheaf k ℓ X) (hA : A.IsLisse) (hA' : A'.IsLisse) (f : A ⟶ A')
        (B N : WeilComplex k ℓ X) (x : (WeilComplex.ihomLisse A hA).obj B ⟶ N),
        (adj A' hA').homEquiv B N ((ihomLissePrecomp f hA hA').app B ≫ x) =
          (adj A hA).homEquiv B N x ≫
            (ihomLissePrecomp (WeilSheaf.dualMap f hA hA') hA'.dual hA.dual).app N := by
  obtain ⟨c, hc⟩ := exists_proEtaleWeilLisseDualTensorEvaluationIso (k := k) (ℓ := ℓ) (X := X)
  let H (A : WeilSheaf k ℓ X) := ProEtaleWeilSheaf.ihomFunctor k ℓ X A.obj
  let adj (A : WeilSheaf k ℓ X) (hA : A.IsLisse) : H A ⊣ H (A.dual hA) :=
    (ProEtaleWeilSheaf.tensorIhomAdjunction k ℓ X (A.dual hA).obj).ofNatIsoLeft (c A hA)
  let derived (A : WeilSheaf k ℓ X) (hA : A.IsLisse) :
      (H A).rightDerivedFunctor ⊣ (H (A.dual hA)).rightDerivedFunctor := by
    have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor A.obj hA
    have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (A.dual hA).obj hA.dual
    exact exactRightDerivedAdjunction (adj A hA)
  let bounded (A : WeilSheaf k ℓ X) (hA : A.IsLisse) :
      WeilComplex.ihomLisse A hA ⊣ WeilComplex.tensorLisse A hA :=
    ObjectProperty.liftFullSubcategoryAdjunction (derived A hA)
      (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor A hA)
      (WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor (A.dual hA) hA.dual)
  refine ⟨bounded, ?_⟩
  intro A A' hA hA' f B N x
  let dualMap := WeilSheaf.dualMap f hA hA'
  let s := (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map f.hom.op
  let t :=
    (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map dualMap.hom.op
  have underived (M : ProEtaleWeilSheaf k ℓ X) :
      (adj A' hA').unit.app M ≫ (H (A'.dual hA')).map (s.app M) =
        (adj A hA).unit.app M ≫ t.app ((H A).obj M) := by
    let a₀ := ProEtaleWeilSheaf.tensorIhomAdjunction k ℓ X (A.dual hA).obj
    let a₁ := ProEtaleWeilSheaf.tensorIhomAdjunction k ℓ X (A'.dual hA').obj
    let tensorMap := ProEtaleWeilSheaf.nativeTensorMap k ℓ X dualMap.hom
    have square : (c A' hA').hom.app M ≫ s.app M = tensorMap.app M ≫ (c A hA).hom.app M :=
      NatTrans.congr_app (hc A A' f hA hA') M
    have mate : conjugateEquiv a₀ a₁ tensorMap = t := (conjugateEquiv a₀ a₁).apply_symm_apply t
    calc
      _ = a₁.homEquiv M _ ((c A' hA').hom.app M ≫ s.app M) :=
        Adjunction.homEquiv_ofNatIsoLeft_apply a₁ (c A' hA') (s.app M)
      _ = a₁.homEquiv M _ (tensorMap.app M ≫ (c A hA).hom.app M) := congrArg _ square
      _ = a₀.homEquiv M _ ((c A hA).hom.app M) ≫ (conjugateEquiv a₀ a₁ tensorMap).app _ :=
        (Adjunction.homEquiv_comp_conjugateEquiv_app a₀ a₁ tensorMap ((c A hA).hom.app M)).symm
      _ = _ := by rw [mate]; rfl
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor A.obj hA
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor A'.obj hA'
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (A.dual hA).obj hA.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (A'.dual hA').obj hA'.dual
  apply ObjectProperty.hom_ext
  exact exactRightDerivedAdjunction_homEquiv (adj A hA) (adj A' hA') s t underived
    (X := B.obj) (Y := N.obj) x.hom

end WeilII
