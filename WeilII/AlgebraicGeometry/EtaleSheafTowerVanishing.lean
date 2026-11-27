module

public import WeilII.AlgebraicGeometry.EtaleSheafTowerMilnor

/-! # Vanishing for the pro-étale limit of an étale tower -/

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace WeilII

universe u

/-- If the level cohomology of an epimorphic étale tower is finite in degree `q` and
vanishes in degree `q + 1`, the pro-étale limit has zero cohomology in degree `q + 1`.
This is the vanishing case of the Milnor sequence (Stacks Project, Tag 07KW). -/
public theorem isZero_functorH_limit_etaleTower (X : Scheme.{u}) (q : ℕ)
    (T : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1})
    (ht : ∀ n : ℕ, Epi (T.map (homOfLE n.le_succ).op))
    (hfin : ∀ n, Finite ((Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj (T.obj n)))
    (hzero : ∀ n, IsZero ((Sheaf.functorH.{u + 1} X.smallEtaleTopology (q + 1)).obj (T.obj n))) :
    IsZero ((Sheaf.functorH.{u + 1} (Scheme.ProEt.topology X) (q + 1)).obj
      (limit (T ⋙ ProEtale.comparisonUpperStar Ab.{u + 1} X))) := by
  let epiTower : ObjectProperty (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
    fun S ↦ ∀ n : ℕ, Epi (S.map (homOfLE n.le_succ).op)
  let S : epiTower.FullSubcategory := ⟨T, ht⟩
  obtain ⟨ι, p, hexact, _⟩ := etaleSheafTower_milnorShortExact X q
  obtain ⟨w, h⟩ := hexact S
  apply h.exact.isZero_X₂
  · exact (finiteTower_mittagLeffler_vanishing
      (T ⋙ Sheaf.functorH.{u + 1} X.smallEtaleTopology q) hfin).2.eq_of_src _ _
  · change p.app S = 0
    apply limit.hom_ext
    intro n
    exact (hzero n).eq_of_tgt _ _

end WeilII
