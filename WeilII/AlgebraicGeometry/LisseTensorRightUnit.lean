module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
import WeilConjectures.WeilSheaf.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseBidual

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The right unit isomorphism of lisse Weil sheaves is natural. By the internal Hom
definition of tensor this is biduality. On the underlying adic sheaves the square
is naturality of the evaluation map. -/
public theorem lisseTensorRightUnit
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    let W := WeilSheaf.adicConstant k ℓ X
    ∃ e : ∀ (A : WeilSheaf k ℓ X) (h : A.IsLisse), A ≅ A.tensorObj W h,
      ∀ (A B : WeilSheaf k ℓ X) (ha : A.IsLisse) (hb : B.IsLisse) (f : A ⟶ B),
        f ≫ (e B hb).hom = (e A ha).hom ≫ WeilSheaf.tensorHom f (𝟙 W) ha hb := by
  intro W
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k ℓ X)
  let ev := ProEtaleWeilSheaf.bifunctorEvaluation k ℓ X
  let e (A : WeilSheaf k ℓ X) (h : A.IsLisse) : A ≅ A.tensorObj W h := by
    have : IsIso (U.map (ev.ev A.obj W.obj)) := ProEtale.IsAdicLisseSheaf.isIso_bidual h
    let iso := @asIso _ _ _ _ (ev.ev A.obj W.obj) (isIso_of_reflects_iso _ U)
    exact ObjectProperty.isoMk _ iso
  refine ⟨e, fun A B ha hb f ↦ ?_⟩
  apply ObjectProperty.hom_ext
  change f.hom ≫ _ = _ ≫ ProEtaleWeilSheaf.ihomMapRight _ (𝟙 _) ≫ _
  erw [ProEtaleWeilSheaf.ihomMapRight_id, Category.id_comp]
  exact ev.naturality f.hom W.obj

end WeilII
