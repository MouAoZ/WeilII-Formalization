module

public import WeilII.AlgebraicGeometry.FiniteProEtaleSystemPresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso

/-! # Detection of derived isomorphisms by the fixed finite quotient modules -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite WeilConjectures.SemilinearSections

namespace WeilII.FiniteProEtaleSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism of derived finite systems is invertible if it is invertible after
reading each finite exponent in fixed module coefficients. This is the homology argument
for `SemilinearSections.Data.detects`, with constant scalar restriction at each exponent. -/
theorem evaluation_detects_iso (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u})
    {M N : Derived ℓ V} (a : M ⟶ N)
    (h : ∀ n, IsIso ((evaluation ℓ V n).map a)) : IsIso a := by
  let J := Scheme.ProEt.topology V
  apply (semilinearDerivedSections.{u+1,u,u+1} J (rings ℓ V) (steps ℓ V)).some.systems.detects
  intro n
  let H := ConstantScalarRestriction.restriction J (Coeff.{u} ℓ n)
  have : Limits.PreservesFiniteLimits H := (ConstantScalarRestriction.exact J _).1
  have : Limits.PreservesFiniteColimits H := (ConstantScalarRestriction.exact J _).2
  let b := (e.{u+1,u,u+1} J (rings ℓ V) (steps ℓ V) n).map a
  have : IsIso (H.mapDerivedCategory.map b) := h n
  exact isIso_of_reflects_iso b H.mapDerivedCategory

end WeilII.FiniteProEtaleSystem
