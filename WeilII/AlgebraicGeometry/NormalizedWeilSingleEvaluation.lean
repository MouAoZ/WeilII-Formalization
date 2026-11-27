module

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
public import WeilII.AlgebraicGeometry.NativeLisseTensorComparison

/-! # Frobenius on the normalized coefficient evaluation in degree zero -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Evaluation normalized on the relative-tensor quotient respects Frobenius after
condensed degree-zero realization. This holds for each normalized coefficient map:
the quotient projection determines it uniquely, and the native normalized evaluation
is a morphism of Weil objects. -/
theorem normalizedEvaluation_frobenius (F G : WeilSheaf k ℓ X) (hF : F.IsLisse)
    (j : (Mod.tensorLeft G.obj.carrier).obj F.obj.carrier ⟶ (F.tensorObj G hF).obj.carrier)
    (hj : Mod.tensorπ F.obj.carrier G.obj.carrier ≫ j.hom =
      Mod.toIhomDual F.obj.carrier G.obj.carrier) :
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let T := ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    H.map (S.map (E.map j)) ≫ singleFrobenius (F.tensorObj G hF).obj =
      singleFrobenius T ≫ S.map (E.map j) := by
  obtain ⟨t, ht⟩ := nativeLisseTensorComparison F G hF
  have h : j = t.hom.hom.f :=
    Mod.tensorLeft_hom_ext _ _ (Mod.hom_ext _ _ (hj.trans ht.symm))
  subst j
  exact singleFrobenius_naturality t.hom

end WeilII.ExternalProduct
