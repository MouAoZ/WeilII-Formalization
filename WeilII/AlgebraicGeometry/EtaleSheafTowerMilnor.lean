module

public import WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison
public import WeilConjectures.CategoryTheory.Finite.FiniteMittagLeffler
import WeilII.AlgebraicGeometry.ProEtaleSheafTowerMilnor
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!
# The Milnor sequence for a tower of étale sheaves

This combines the product computation in `WeilConjectures.Algebra.Homology.DerivedCategory.Ext`
with étale to pro-étale cohomology comparison and the Roos computation of the derived limit
(Stacks Project, Tag 07KW).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace WeilII

universe u

/-- For an epimorphic tower of abelian étale sheaves on a scheme, the cohomology of the
pro-étale limit fits in the natural Milnor short exact sequence in every degree `q + 1`.
Tower index `n` represents level `n + 1`. The last equation identifies each projection of
the right arrow with restriction to that level followed by inverse site comparison.

The proof follows the product argument in the upstream file `Ext/TowerLimitIso.lean`, using
pro-étale repleteness, `ProEtale.cohomologyComparisonAddEquiv`, and the Roos computation
(Stacks Project, Tag 07KW).
Pull the tower back to the pro-étale site. Pullback preserves cokernels, so its transitions
are epimorphisms. On the product P of the pulled-back sheaves let d be one minus the shift
induced by the transitions. A map to P factors through the kernel of d precisely when its
components form a cone, so this kernel is the inverse limit M. Repleteness makes d epic,
giving a short exact sequence M ⟶ P ⟶ P.

Countable products on the pro-étale site are exact. Thus Ext from the constant integer
sheaf into P is the product of the levelwise Ext groups, via the projections. In degree j,
the map induced by d sends a family x to the family with components
xₙ − Hʲ(tₙ)(xₙ₊₁), where tₙ is the transition. Write Dⱼ for this map. In the long exact
cohomology sequence the connecting map therefore induces an injection from coker D_q
to H^(q+1)(M). Its image is the kernel of the map induced by the limit projections, and
the image of the latter map is ker D_(q+1).

Levelwise site comparison commutes with the transitions, hence identifies each Dⱼ with
the same difference map on étale cohomology. Its kernel is the group of compatible
families. In degree q its cokernel is naturally the first derived inverse limit by Roos.
These identifications give the displayed sequence and its projection formula. A tower
morphism commutes with the shifts and induces a morphism of the product short exact
sequences. Naturality of the connecting map descends through the cokernels, and
naturality of the limit projections gives the other square. -/
public theorem etaleSheafTower_milnorShortExact (X : Scheme.{u}) (q : ℕ) :
    let epiTower : ObjectProperty (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
      fun T ↦ ∀ n : ℕ, Epi (T.map (homOfLE n.le_succ).op)
    let etaleH (j : ℕ) := epiTower.ι ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (Sheaf.functorH.{u + 1, u + 1} X.smallEtaleTopology j)
    let pull := ProEtale.comparisonUpperStar Ab.{u + 1} X
    let proH := Sheaf.functorH.{u + 1, u + 1} (Scheme.ProEt.topology X) (q + 1)
    let middle := epiTower.ι ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj pull ⋙ lim ⋙ proH
    letI := roosTowerEnoughInjectives.{u + 1}
    letI := roosLimitAdditive.{u + 1}
    let limOne := (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerived 1
    ∃ (ι : etaleH q ⋙ limOne ⟶ middle) (p : middle ⟶ etaleH (q + 1) ⋙ lim),
      (∀ T, ∃ w : ι.app T ≫ p.app T = 0, (ShortComplex.mk (ι.app T) (p.app T) w).ShortExact) ∧
      ∀ (T : epiTower.FullSubcategory) (n : ℕᵒᵖ),
        p.app T ≫ limit.π ((etaleH (q + 1)).obj T) n =
          proH.map (limit.π (T.obj ⋙ pull) n) ≫ AddCommGrpCat.ofHom
            (ProEtale.cohomologyComparisonAddEquiv X (T.obj.obj n) (q + 1)).symm.toAddMonoidHom := by
  classical
  intro epiTower etaleH pull proH middle limOne
  let F := epiTower.ι ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj pull
  let H (j : ℕ) := Sheaf.functorH.{u + 1, u + 1} (Scheme.ProEt.topology X) j
  let A (j : ℕ) := F ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (H j)
  have hF (T : epiTower.FullSubcategory) (n : ℕ) :
      Epi ((F.obj T).map (homOfLE n.le_succ).op) := by
    have := T.property n
    exact pull.map_epi (T.obj.map (homOfLE n.le_succ).op)
  obtain ⟨i, p, h, hp⟩ := proEtaleSheafTower_milnorShortExact X F hF q
  let site (j : ℕ) : Sheaf.functorH.{u + 1, u + 1} X.smallEtaleTopology j ≅ pull ⋙ H j :=
    NatIso.ofComponents (fun B ↦ (ProEtale.cohomologyComparisonAddEquiv X B j).toAddCommGrpIso)
      fun f ↦ by ext x; exact ProEtale.cohomologyComparison_map X f j x
  let level (j : ℕ) (T : epiTower.FullSubcategory) : (etaleH j).obj T ≅ (A j).obj T :=
    Functor.isoWhiskerLeft T.obj (site j)
  let comparison (j : ℕ) : etaleH j ≅ A j :=
    NatIso.ofComponents (level j) fun f ↦ by
      apply NatTrans.ext
      funext n
      exact (site j).hom.naturality (f.hom.app n)
  let e := Functor.isoWhiskerRight (comparison q) limOne
  let e' := Functor.isoWhiskerRight (comparison (q + 1)) lim
  refine ⟨e.hom ≫ i, p ≫ e'.inv, ?_, ?_⟩
  · intro T
    obtain ⟨z, hz⟩ := h T
    have zero : (e.hom ≫ i).app T ≫ (p ≫ e'.inv).app T = 0 := by
      simp only [NatTrans.comp_app, Category.assoc, reassoc_of% z, zero_comp, comp_zero]
    refine ⟨zero, ShortComplex.shortExact_of_iso ?_ hz⟩
    exact ShortComplex.isoMk (e.app T).symm (Iso.refl _) (e'.app T).symm
      (by simp) (by simp)
  · intro T n
    change (p.app T ≫ limMap (level (q + 1) T).inv) ≫ _ = _
    rw [Category.assoc, limMap_π, ← Category.assoc, hp]
    rfl

end WeilII
