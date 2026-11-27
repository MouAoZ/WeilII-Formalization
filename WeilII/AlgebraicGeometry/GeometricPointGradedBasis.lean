module

public import WeilConjectures.TraceFormula.PointTrace
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Bases of the graded Hom spaces on a separably closed point -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale.CondensedRing CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace WeilII

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]

/-- In a finite presentation by shifted units, the inclusions in degree `n` form a basis of
degree-`n` cohomology. The shift index of a degree-`n` generator is `-n`. -/
theorem exists_geometricPointGradedBasis {J : Type*} [Fintype J] (deg : J → ℤ)
    (A : DerivedCategory (PointMod ℓ Ω))
    (inc : ∀ i, shiftedUnit ℓ Ω (-deg i) ⟶ A) (pr : ∀ i, A ⟶ shiftedUnit ℓ Ω (-deg i))
    (total : ∑ i, pr i ≫ inc i = 𝟙 A)
    (diag : ∀ i, inc i ≫ pr i = 𝟙 _) (off : ∀ i j, i ≠ j → inc i ≫ pr j = 0) :
    ∃ b : ∀ n, Module.Basis {i // deg i = n} (PadicAlgCl ℓ) ((gradedHom ℓ Ω (-n)).obj A),
      ∀ i, gradedHomHom ℓ Ω (b (deg i) ⟨i, rfl⟩) = inc i := by
  classical
  let H (n : ℤ) := gradedHom ℓ Ω (-n)
  let v (n : ℤ) (i : {i // deg i = n}) : (H n).obj A :=
    gradedHomMk ℓ Ω (eqToHom (congrArg (fun k ↦ shiftedUnit ℓ Ω (-k)) i.2.symm) ≫ inc i.1)
  have hli (n : ℤ) : LinearIndependent (PadicAlgCl ℓ) (v n) := by
    refine Fintype.linearIndependent_iff.mpr fun c hc j ↦ ?_
    obtain ⟨j, rfl⟩ := j
    let L := ((shiftedUnitEquiv ℓ Ω (-deg j)).symm.toLinearMap).comp ((H (deg j)).map (pr j)).hom
    have proj (i : {i // deg i = deg j}) : L (v _ i) = if i = ⟨j, rfl⟩ then 1 else 0 := by
      split_ifs with hij
      · subst i
        apply (shiftedUnitEquiv ℓ Ω _).injective
        change (shiftedUnitEquiv ℓ Ω _) ((shiftedUnitEquiv ℓ Ω _).symm _) = _
        rw [LinearEquiv.apply_symm_apply]
        change gradedHomHom ℓ Ω (((H _).map (pr _)).hom _) = gradedHomHom ℓ Ω (shiftedUnitEquiv ℓ Ω _ 1)
        rw [gradedHomHom_map_apply, gradedHomHom_shiftedUnitEquiv]
        change (𝟙 _ ≫ inc _) ≫ pr _ = _
        simp [diag]
      · have hz : ((H (deg j)).map (pr j)).hom (v _ i) = 0 := by
          change (_ ≫ inc i.1) ≫ pr j = 0
          rw [Category.assoc, off _ _ (fun e ↦ hij (Subtype.ext e)), Limits.comp_zero]
        simp [L, hz]
    have h := congrArg L hc
    simp only [map_sum, map_smul, proj, map_zero] at h
    simpa [smul_ite] using h
  have hsp (n : ℤ) : ⊤ ≤ Submodule.span (PadicAlgCl ℓ) (Set.range (v n)) := by
    intro x _
    have hx : x = ∑ i, ((H n).map (inc i)).hom (((H n).map (pr i)).hom x) := by
      change gradedHomHom ℓ Ω x = ∑ i, (gradedHomHom ℓ Ω x ≫ pr i) ≫ inc i
      rw [show ∑ i, (gradedHomHom ℓ Ω x ≫ pr i) ≫ inc i =
        gradedHomHom ℓ Ω x ≫ ∑ i, pr i ≫ inc i by simp [Preadditive.comp_sum]]
      rw [total, Category.comp_id]
    rw [hx]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : deg i = n
    · subst n
      obtain ⟨c, hc⟩ := (shiftedUnitEquiv ℓ Ω (-deg i)).surjective (((H _).map (pr i)).hom x)
      rw [← hc]
      change ((H _).map (inc i)).hom (c • gradedHomMk ℓ Ω (𝟙 _)) ∈ _
      rw [map_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨i, rfl⟩, rfl⟩
    · have hs := subsingleton_hom_shiftedUnit ℓ Ω (-n) (-deg i) (by omega)
      have hz : ((H n).map (pr i)).hom x = 0 := hs.elim _ _
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  refine ⟨fun n ↦ Module.Basis.mk (hli n) (hsp n), fun i ↦ ?_⟩
  rw [Module.Basis.mk_apply]
  exact Category.id_comp _

end WeilII
