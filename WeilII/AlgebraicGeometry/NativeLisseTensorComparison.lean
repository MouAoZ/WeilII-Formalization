module

public import WeilII.AlgebraicGeometry.AdicLisseTensorEvaluation
public import WeilConjectures.WeilSheaf.TensorObjPairing
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-! # Evaluation on the native tensor product of Weil sheaves

The two Weil-equivariant pairings in `WeilSheaf/TensorObjPairing.lean` and
`WeilSheaf/TensorHomAdjunction.lean` let the lisse evaluation isomorphism descend. -/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Endofunctor

namespace WeilII

universe u

/-- The ordinary relative tensor of two native Weil sheaves is isomorphic, by evaluation,
to the internal-Hom model of their tensor when the first sheaf is lisse.
The quotient projection and the evaluation pairing both intertwine Frobenius. Precomposing
with the pulled-back quotient therefore proves equivariance of the descended evaluation
isomorphism. Source: `ProEtaleWeilSheaf.tensorπ_str` and `WeilSheaf.toIhomDual_str`. -/
theorem nativeLisseTensorComparison
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F G : WeilSheaf k ℓ X) (hF : F.IsLisse) :
    ∃ j : ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj ≅ (F.tensorObj G hF).obj,
      Mod.tensorπ F.obj.carrier G.obj.carrier ≫ j.hom.hom.f.hom =
        Mod.toIhomDual F.obj.carrier G.obj.carrier := by
  obtain ⟨j, hj⟩ := adicLisseTensorEvaluation F.obj.carrier G.obj.carrier hF
  let T := ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj
  let N := F.tensorObj G hF
  let Fr := ProEtale.lowerStar (WeilCoefficients.{u} ℓ)
    (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv
  have comm : (WeilSheaf.frobeniusPullback k ℓ X).map j.hom ≫ N.obj.str.hom =
      T.str.hom ≫ j.hom := by
    apply ProEtaleWeilSheaf.frobeniusPullback_tensor_hom_ext (P := F.obj) (M := G.obj)
    change _ ≫ Fr.map (Mod.tensorπ _ _) ≫ Fr.map j.hom.hom ≫ _ =
      _ ≫ Fr.map (Mod.tensorπ _ _) ≫ T.str.hom.hom ≫ j.hom.hom
    erw [← Fr.map_comp_assoc, hj, ← reassoc_of% (ProEtaleWeilSheaf.tensorπ_str F.obj G.obj),
      hj, WeilSheaf.toIhomDual_str F G hF]
    rfl
  exact ⟨IsoAlgebra.isoMk j comm, hj⟩

end WeilII
