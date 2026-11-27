module

public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import WeilConjectures.CategoryTheory.Limits.TowerLimitShortComplex
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

open CategoryTheory Limits Opposite

namespace WeilII

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism to the strict Roos complex has the prescribed projections if its
mapping-fiber first coordinate induces each of the specified tower legs. -/
@[expose] public def HasRoosProjections
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {T : ℕᵒᵖ ⥤ CochainComplex A ℤ} {L : CochainComplex A ℤ}
    (ι : L ⟶ WeilConjectures.integralOperationsRoos T) (legs : ∀ n : ℕ, L ⟶ T.obj (op n)) : Prop :=
  ∀ n : ℕ, ι ≫ CochainComplex.mappingCocone.fst (towerTransitionEndomorphism
    (K := fun j ↦ T.obj (op j)) (WeilConjectures.integralOperationsTowerStep T)) ≫
    Pi.π (fun j ↦ T.obj (op j)) n = legs n

/-- For an epimorphic tower in a replete abelian category, a limiting cone placed in
degree zero maps quasi-isomorphically to the strict Roos complex with its given legs.
This is the kernel presentation of the inverse limit in Stacks, Tag 08TC. -/
public theorem singleTowerRoosAugmentation
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] (hrep : EpiπAppZeroOfEpi A)
    (T : ℕᵒᵖ ⥤ A) (ht : ∀ n : ℕ, Epi (T.map (homOfLE n.le_succ).op))
    (c : Cone T) (hc : IsLimit c) :
    let S := CochainComplex.singleFunctor A (0 : ℤ)
    let K := T ⋙ S
    ∃ ι : S.obj c.pt ⟶ WeilConjectures.integralOperationsRoos K, QuasiIso ι ∧
      HasRoosProjections (T := K) ι (fun n ↦ S.map (c.π.app (op n))) := by
  classical
  intro S K
  let δ := towerTransitionEndomorphism (K := fun n ↦ K.obj (op n))
    (WeilConjectures.integralOperationsTowerStep K)
  let F := fun n : ℕ ↦ T.obj (op n)
  let s := towerProductShift (K := F) (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ Pi.π F n = Pi.π F (n + 1) ≫ T.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  have he : Epi (𝟙 _ - s) := epi_one_sub_of_epiπAppZeroOfEpi hrep ht (productIsProduct F) s hs
  have : PreservesLimitsOfShape (Discrete ℕ) S :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single A (.up ℤ) 0))
  have : PreservesLimitsOfShape ℕᵒᵖ S :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single A (.up ℤ) 0))
  let G := fun n : ℕ ↦ K.obj (op n)
  let t := towerProductShift (K := G) (WeilConjectures.integralOperationsTowerStep K)
  have ht' (n : ℕ) : t ≫ Pi.π G n = Pi.π G (n + 1) ≫ K.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  let e := asIso (piComparison S F)
  have hδ : e.hom ≫ δ = S.map (𝟙 _ - s) ≫ e.hom :=
    (map_towerTransitionEndomorphism_comp_piComparison S F (fun n ↦ T.map (homOfLE n.le_succ).op)).symm
  have : Epi (S.map (𝟙 _ - s)) := S.map_epi _
  have : Epi δ := epi_of_epi_fac hδ
  let d := S.mapCone c
  have hd : IsLimit d := isLimitOfPreserves S hc
  let hk := Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct G) t ht' hd
  let i : d.pt ≅ kernel δ := hk.conePointUniqueUpToIso (limit.isLimit (parallelPair δ 0))
  have hi : i.hom ≫ kernel.ι δ = Fan.IsLimit.lift (productIsProduct G)
      (fun n ↦ d.π.app (op n)) :=
    hk.conePointUniqueUpToIso_hom_comp (limit.isLimit (parallelPair δ 0)) WalkingParallelPair.zero
  let := HasDerivedCategory.standard A
  obtain ⟨κ, hκ, hq, _⟩ := CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi
    δ (fun _ ↦ inferInstance)
  have hfst : κ ≫ CochainComplex.mappingCocone.fst δ = kernel.ι δ := by
    apply HomologicalComplex.hom_ext
    intro p
    have hf : (CochainComplex.mappingCocone.fst δ).f p =
        ((CochainComplex.mappingCone δ).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
        HomologicalComplex.homotopyCofiber.fstX δ (p - 1) p (by change p - 1 + 1 = p; omega) := by
      simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.fst,
        CochainComplex.shiftFunctorObjXIso,
        CochainComplex.HomComplex.Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p - 1) (by omega)]
    change κ.f p ≫ (CochainComplex.mappingCocone.fst δ).f p = _
    rw [hf]
    exact (hκ p).2
  refine ⟨i.hom ≫ κ, quasiIso_comp _ _ (hφ' := hq), fun n ↦ ?_⟩
  rw [Category.assoc, ← Category.assoc κ, hfst, ← Category.assoc, hi]
  exact Fan.IsLimit.fac (productIsProduct G) _ n

end WeilII
