module

public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-! # Detecting invertibility of a right adjoint comparison by a supported triangle -/

open CategoryTheory CategoryTheory.Pretriangulated

namespace WeilII

/-- The mate of a direct-image comparison is invertible at an object whose transported counit
is the first arrow of a distinguished triangle right orthogonal to the closed image at its
third vertex. Use the representation by the first vertex of a supported triangle from
`CategoryTheory/Triangulated/Recollement`. Under adjunction its representing bijection is
composition with the mate, by the mate-counit equation. Yoneda detects invertibility. -/
public theorem isIso_rightAdjointExchange_app_of_supportTriangle
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Preadditive D] [Limits.HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {I : A ⥤ B} {J : C ⥤ D} {R : B ⥤ A} {S : D ⥤ C} (a : I ⊣ R) (b : J ⊣ S)
    {U : A ⥤ C} {V : B ⥤ D} (κ : I ⋙ V ≅ U ⋙ J) (hJ : J.FullyFaithful)
    (M : B) {P : D} {g : V.obj M ⟶ P}
    {w : P ⟶ (V.obj (I.obj (R.obj M)))⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (V.map (a.counit.app M)) g w ∈ distTriang D)
    (hP : ∀ (N : C) (n : ℤ), Subsingleton ((J.obj N)⟦n⟧ ⟶ P)) :
    IsIso ((Adjunction.rightAdjointExchange a b κ).app M) := by
  let m := (Adjunction.rightAdjointExchange a b κ).app M
  have hc : J.map m ≫ b.counit.app (V.obj M) =
      κ.inv.app (R.obj M) ≫ V.map (a.counit.app M) :=
    mateEquiv_counit a b κ.inv M
  apply isIso_of_yoneda_map_bijective
  intro N
  let rep := representableByOfDistTriang hJ hT hP (κ.symm.app (R.obj M))
  let e := rep.homEquiv.trans (b.homEquiv N (V.obj M))
  have he (f : N ⟶ U.obj (R.obj M)) : e f = f ≫ m := by
    apply (b.homEquiv N (V.obj M)).symm.injective
    change (b.homEquiv _ _).symm ((b.homEquiv _ _) _) = _
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    change J.map f ≫ κ.inv.app (R.obj M) ≫ V.map (a.counit.app M) =
      J.map (f ≫ m) ≫ b.counit.app (V.obj M)
    rw [J.map_comp, Category.assoc, hc]
  exact (funext he) ▸ e.bijective

end WeilII
