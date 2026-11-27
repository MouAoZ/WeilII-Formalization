module

public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Computing a Milnor limit by a strict Roos complex -/

open CategoryTheory Limits Pretriangulated Opposite

namespace WeilII

/-- A Milnor limit of a tower presented by a strict tower of cochain complexes is
isomorphic to its Roos mapping fibre. The hypothesis on products makes the localization
of the product fan limiting. The isomorphism of fans commutes with the transition
shifts by its projection equations, and hence identifies the second arrows of the
Milnor and mapping-cocone triangles. Complete it to an isomorphism on the first terms.
Sources: Stacks 08TC and the pinned `DerivedCategory.isLimitFanQ`. -/
public theorem homotopyLimitIsoStrictRoos
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    {F : ℕᵒᵖ ⥤ DerivedCategory A} {c : Cone F} (hc : IsHomotopyLimit c)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (e : F ≅ T ⋙ DerivedCategory.Q) :
    Nonempty (c.pt ≅ DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos T)) := by
  let Q := DerivedCategory.Q (C := A)
  let G := T ⋙ Q
  let c' : Cone G := ⟨c.pt, c.π ≫ e.hom⟩
  have hc' := IsHomotopyLimit.of_iso e hc c' (Iso.refl _) (fun n ↦ by simp [c'])
  obtain ⟨P, hP, δ, hΔ⟩ := hc'
  let K (n : ℕ) := T.obj (op n)
  let P' : Fan (fun n : ℕ ↦ G.obj (op n)) := Fan.mk (Q.obj (∏ᶜ K)) (fun n ↦ Q.map (Pi.π K n))
  let hP' : IsLimit P' := DerivedCategory.isLimitFanQ K
  let g := hP.conePointUniqueUpToIso hP'
  have hg (n : ℕ) : g.hom ≫ Q.map (Pi.π K n) = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp hP' ⟨n⟩
  let t := towerTransitionEndomorphism (K := K) (WeilConjectures.integralOperationsTowerStep T)
  have ht : (𝟙 P.pt - towerShift hP) ≫ g.hom = g.hom ≫ Q.map t := by
    apply Fan.IsLimit.hom_ext hP' _ _
    intro n
    change _ ≫ Q.map (Pi.π K n) = _ ≫ Q.map (Pi.π K n)
    have hstep := (towerTransitionEndomorphism_eq_iff (K := K) (WeilConjectures.integralOperationsTowerStep T) t).1 rfl n
    rw [Category.assoc, hg, Preadditive.sub_comp, Category.id_comp, towerShift, Fan.IsLimit.fac,
      Category.assoc, ← Q.map_comp, hstep, Q.map_sub, Preadditive.comp_sub, hg, Q.map_comp,
      ← Category.assoc, hg]
    rfl
  have hC := DerivedCategory.mappingCocone_triangle_distinguished t
  obtain ⟨a, ha, hb⟩ := complete_distinguished_triangle_morphism₁ _ _ hΔ hC g.hom g.hom ht
  have haIso : IsIso a := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a g.hom g.hom ha ht hb) hΔ hC
    g.isIso_hom g.isIso_hom
  exact ⟨@asIso _ _ _ _ a haIso⟩

end WeilII
