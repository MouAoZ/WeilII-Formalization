module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import WeilConjectures.CategoryTheory.Limits.TowerLimitShortComplex
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-! # Milnor's short exact sequence for epimorphic towers on the pro-étale site -/

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace WeilII

universe u v w

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- A family of epimorphic towers of abelian pro-étale sheaves has a natural Milnor
sequence. Its right arrow is induced by the projections of the inverse limit.
The product sequence and the long exact sequence give the kernel and cokernel
description. The Roos isomorphism identifies the cokernel with the first derived limit
(Stacks Project, Tags 0CQD and 07KW). -/
public theorem proEtaleSheafTower_milnorShortExact (X : Scheme.{u}) {D : Type v}
    [Category.{w} D] (F : D ⥤ (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (hF : ∀ (T : D) (n : ℕ), Epi ((F.obj T).map (homOfLE n.le_succ).op)) (q : ℕ) :
    let H (j : ℕ) := Sheaf.functorH.{u + 1, u + 1} (Scheme.ProEt.topology X) j
    let A (j : ℕ) := F ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (H j)
    let M := F ⋙ lim ⋙ H (q + 1)
    letI := roosTowerEnoughInjectives.{u + 1}
    letI := roosLimitAdditive.{u + 1}
    let L := (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerived 1
    ∃ (i : A q ⋙ L ⟶ M) (p : M ⟶ A (q + 1) ⋙ lim),
      (∀ T, ∃ z : i.app T ≫ p.app T = 0, (ShortComplex.mk _ _ z).ShortExact) ∧
      ∀ T n, p.app T ≫ limit.π ((A (q + 1)).obj T) n =
        (H (q + 1)).map (limit.π (F.obj T) n) := by
  classical
  intro H A M L
  let := roosTowerEnoughInjectives.{u + 1}
  let := roosLimitAdditive.{u + 1}
  -- Repleteness makes one minus the shift epic on the product of each tower.
  let S (T : D) := towerLimitShortComplex (F.obj T)
  have hs (T : D) : (S T).ShortExact :=
    towerLimitShortComplex_shortExact _ (epi_one_sub_of_epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_ab (hF T) (productIsProduct _)
      (towerProductShift _) fun n ↦ Pi.lift_comp_π _ n)
  -- Compute cohomology of this product using Ext from the constant integer sheaf.
  let family (T : D) (n : ℕ) := (F.obj T).obj (op n)
  let c (j : ℕ) (T : D) := piComparison (H j) (family T)
  have hcIso (j : ℕ) (T : D) : IsIso (c j T) := by
    let _ := HasDerivedCategory.standard (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    let e := Concrete.productEquiv (fun n ↦ (H j).obj (family T n))
    apply (ConcreteCategory.isIso_iff_bijective _).2
    apply (Function.Bijective.of_comp_iff' e.bijective _).1
    have he : e ∘ (c j T) = fun x n ↦ Sheaf.H.map (Pi.π (family T) n) j x := by
      funext x n
      simp only [Function.comp_apply, e, Concrete.productEquiv_apply_apply]
      exact ConcreteCategory.congr_hom (piComparison_comp_π (H j) (family T) n) x
    rw [he]
    exact Abelian.Ext.bijective_comp_mk₀_proj _ (productIsProduct (family T)) j
  -- In product coordinates the induced endomorphism is the Roos differential.
  let d (j : ℕ) (T : D) := roosMap ((A j).obj T)
  have hc (j : ℕ) (T : D) :
      (H j).map (S T).g ≫ c j T = c j T ≫ d j T :=
    map_towerTransitionEndomorphism_comp_piComparison (H j) (family T) _
  let δ (T : D) := AddCommGrpCat.ofHom (Sheaf.H.δ (hs T) q (q + 1) rfl)
  let boundary (T : D) := inv (c q T) ≫ δ T
  let incl (T : D) := (H (q + 1)).map (S T).f ≫ c (q + 1) T
  have dδ (T : D) : d q T ≫ boundary T = 0 := by
    rw [← cancel_epi (c q T), ← Category.assoc, ← hc]
    simp only [boundary, Category.assoc, IsIso.hom_inv_id_assoc, comp_zero]
    exact (Sheaf.H.longSequence_exact (hs T) q (q + 1) rfl).zero 1
  let left (T : D) := cokernel.desc (d q T) (boundary T) (dδ T)
  let right (T : D) : M.obj T ⟶ limit ((A (q + 1)).obj T) :=
    limit.lift _ ((H (q + 1)).mapCone (limit.cone (F.obj T)))
  have proj (T : D) (n : ℕᵒᵖ) : right T ≫ limit.π ((A (q + 1)).obj T) n =
      (H (q + 1)).map (limit.π (F.obj T) n) := limit.lift_π _ _
  -- Truncate the long exact sequence at the cokernel and the kernel of these differentials.
  have short (T : D) : ∃ z : left T ≫ right T = 0, (ShortComplex.mk _ _ z).ShortExact := by
    have zero₁ : δ T ≫ (H (q + 1)).map (S T).f = 0 :=
      (Sheaf.H.longSequence_exact (hs T) q (q + 1) rfl).zero 2
    have zero₂ : (H (q + 1)).map (S T).f ≫ (H (q + 1)).map (S T).g = 0 := by
      rw [← Functor.map_comp, (S T).zero, Functor.map_zero]
    have hbi : boundary T ≫ incl T = 0 := by simp [boundary, incl, reassoc_of% zero₁]
    have hid : incl T ≫ d (q + 1) T = 0 := by
      dsimp only [incl]
      rw [Category.assoc, ← hc, ← Category.assoc, zero₂, zero_comp]
    refine ShortComplex.shortExact_cokernelDesc_of_exact (dδ T) hbi hid ?_ ?_ ?_
      (towerLimitShortComplex.isLimit ((A (q + 1)).obj T)) (right T) ?_
    · apply ShortComplex.exact_of_iso _ (Sheaf.H.longSequence_exact₃' (hs T) q (q + 1) rfl)
      exact ShortComplex.isoMk (asIso (c q T)) (asIso (c q T)) (Iso.refl _)
        (hc q T).symm (by simp [boundary, δ])
    · apply ShortComplex.exact_of_iso _ (Sheaf.H.longSequence_exact₁' (hs T) q (q + 1) rfl)
      exact ShortComplex.isoMk (asIso (c q T)) (Iso.refl _) (asIso (c (q + 1) T))
        (by simp [boundary, δ]) (by simp [incl, H])
    · apply ShortComplex.exact_of_iso _ (Sheaf.H.longSequence_exact₂' (hs T) (q + 1))
      exact ShortComplex.isoMk (Iso.refl _) (asIso (c (q + 1) T)) (asIso (c (q + 1) T))
        (by simp [incl, H]) (hc (q + 1) T).symm
    · apply Pi.hom_ext
      intro n
      change (right T ≫ Pi.lift _) ≫ _ = ((H (q + 1)).map (Pi.lift _) ≫ c (q + 1) T) ≫ _
      rw [Category.assoc]
      erw [Pi.lift_comp_π]
      rw [proj, Category.assoc, piComparison_comp_π (H (q + 1)) (family T),
        ← Functor.map_comp]
      erw [Pi.lift_comp_π]
  -- Descend naturality of the connecting map through the epic cokernel projection.
  obtain ⟨_, _, e, he, _⟩ := derivedLimitRoosAbelianGroups.{u + 1}
  let i : A q ⋙ L ⟶ M :=
    { app := fun T ↦ (e ((A q).obj T)).hom ≫ left T
      naturality := by
        intro T U f
        let φ := F.map f
        let ψ := (A q).map f
        obtain ⟨h, _, hnat⟩ := he _ _ ψ
        change L.map ψ ≫ (e _).hom ≫ left U = ((e _).hom ≫ left T) ≫ M.map f
        rw [← Category.assoc, hnat, Category.assoc, Category.assoc]
        congr 1
        apply (cancel_epi (cokernel.π (d q T))).mp
        change cokernel.π (d q T) ≫ cokernel.map _ _ _ _ h ≫ left U = _
        simp only [left, cokernel.map, cokernel.π_desc_assoc, Category.assoc]
        erw [cokernel.π_desc]
        let a := Limits.Pi.map fun n : ℕ ↦ φ.app (op n)
        let b := Limits.Pi.map fun n : ℕ ↦ ψ.app (op n)
        have hn : (H q).map a ≫ c q U = c q T ≫ b :=
          map_piMap_comp_piComparison (H q) _
        have hn' : b ≫ inv (c q U) = inv (c q T) ≫ (H q).map a := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact hn.symm
        change b ≫ inv (c q U) ≫ δ U = (inv (c q T) ≫ δ T) ≫ M.map f
        rw [← Category.assoc, hn', Category.assoc, Category.assoc]
        congr 1
        apply ConcreteCategory.hom_ext
        intro x
        exact Sheaf.H.δ_naturality q (q + 1) rfl (hs T) (hs U) (towerLimitShortComplexMap φ) x }
  let p : M ⟶ A (q + 1) ⋙ lim :=
    { app := right
      naturality := by
        intro T U f
        apply limit.hom_ext
        intro n
        change ((H (q + 1)).map (limMap (F.map f)) ≫ right U) ≫ _ =
          (right T ≫ limMap ((A (q + 1)).map f)) ≫ _
        rw [Category.assoc, proj, ← Functor.map_comp, limMap_π, Functor.map_comp,
          Category.assoc, limMap_π, ← Category.assoc, proj]
        rfl }
  refine ⟨i, p, ?_, proj⟩
  intro T
  obtain ⟨z, hz⟩ := short T
  have z' : i.app T ≫ p.app T = 0 := by
    change ((e _).hom ≫ left T) ≫ right T = 0
    rw [Category.assoc, z, comp_zero]
  refine ⟨z', ShortComplex.shortExact_of_iso ?_ hz⟩
  exact ShortComplex.isoMk (e _).symm (Iso.refl _) (Iso.refl _) (by simp [i]) (by simp [p])

end WeilII
