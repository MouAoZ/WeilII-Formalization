module

public import WeilII.AlgebraicGeometry.CompactSupportBinaryKunnethDecomposition
public import WeilII.LinearAlgebra.FrobeniusModuleEquivariantEmbedding
import WeilConjectures.WeilSheaf.TateTwistCohomology

open AlgebraicGeometry CategoryTheory

namespace WeilII

variable
    {k : Type*} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y P : Scheme} [overX : X.Over (Spec (.of k))] [overY : Y.Over (Spec (.of k))]
    [overP : P.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (P ↘ Spec (.of k))] [LocallyOfFiniteType (P ↘ Spec (.of k))]
    [QuasiCompact (P ↘ Spec (.of k))]

/-- All bidegrees and coefficients for a fixed pair of projections. Keeping the projections
as parameters lets us pass from the slice category to its underlying scheme maps. -/
private def SummandProperty
    (p : P ⟶ X) (s : P ⟶ Y) [p.IsOver (Spec (.of k))] [s.IsOver (Spec (.of k))] : Prop :=
    ∀ (L : WeilSheaf k ℓ X) (M : WeilSheaf k ℓ Y) (hL : L.IsLisse) (_hM : M.IsLisse)
    (N : WeilSheaf k ℓ P) (_iso : ((WeilSheaf.upperStar p).obj L).tensorObj
      ((WeilSheaf.upperStar s).obj M) (hL.upperStar p) ≅ N) (a b : ℤ),
    let T := (L.compactlySupportedCohomology a).tensor (M.compactlySupportedCohomology b)
    let W := N.compactlySupportedCohomology (a + b)
    T.Embeds W

attribute [local instance] instOverLeftSchemeSpecOf_weilII instIsOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

/-- The bidegree `(a,b)` summand of binary compact-support Künneth, transported along
a specified Weil isomorphism of the product coefficient. Its inclusion is injective
since projection onto its component is a left inverse. The direct-sum Frobenius acts on
this component by tensor Frobenius, and transport along a Weil isomorphism is equivariant.
See SGA 4, XVII, 5.4.3, and Zhang's deduction of Theorem 1.1 on p. 2. -/
public theorem compactSupportKunnethSummand
    (p : P ⟶ X) (s : P ⟶ Y) [over_p : p.IsOver (Spec (.of k))] [over_s : s.IsOver (Spec (.of k))]
    (product : IsPullback s p (Y ↘ Spec (.of k)) (X ↘ Spec (.of k)))
    (L : WeilSheaf k ℓ X) (M : WeilSheaf k ℓ Y) (hL : L.IsLisse) (hM : M.IsLisse)
    (N : WeilSheaf k ℓ P) (coeff : ∃ h : ((WeilSheaf.upperStar p).obj L).IsLisse,
      Nonempty (((WeilSheaf.upperStar p).obj L).tensorObj ((WeilSheaf.upperStar s).obj M) h ≅ N))
    (a b : ℤ) :
    let T := (L.compactlySupportedCohomology a).tensor (M.compactlySupportedCohomology b)
    let W := N.compactlySupportedCohomology (a + b)
    T.Embeds W := by
  let X' := Over.mk (X ↘ Spec (.of k))
  let Y' := Over.mk (Y ↘ Spec (.of k))
  let P' := Over.mk (P ↘ Spec (.of k))
  let p' : P' ⟶ X' := Over.homMk p (comp_over p _)
  let s' : P' ⟶ Y' := Over.homMk s (comp_over s _)
  have fromSlice {A B C : Over (Spec (.of k))}
      [IsSeparated A.hom] [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
      [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
      [IsSeparated C.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
      (f : C ⟶ A) (g : C ⟶ B) (square : IsPullback g.left f.left B.hom A.hom) :
      SummandProperty (k := k) (ℓ := ℓ) f.left g.left := by
    intro L M hL hM N iso a b
    classical
    obtain ⟨e, _, hf⟩ := compactSupportBinaryKunnethDecomposition f g square L M hL hM (a + b)
    let i : {q : ℤ × ℤ // q.1 + q.2 = a + b} := ⟨(a, b), rfl⟩
    let T := fun j : {q : ℤ × ℤ // q.1 + q.2 = a + b} ↦
      (L.compactlySupportedCohomology j.1.1).tensor (M.compactlySupportedCohomology j.1.2)
    let inc := DirectSum.lof (PadicAlgCl ℓ) _ (fun j ↦ (T j).carrier) i
    let c := WeilSheaf.compactlySupportedCohomologyEquivOfIso iso (a + b)
    let proj := DirectSum.component (PadicAlgCl ℓ) _ (fun j ↦ (T j).carrier) i
    have leftInv : Function.LeftInverse proj inc :=
      fun x ↦ DFunLike.congr_fun (DirectSum.component_comp_lof_same (M := fun j ↦ (T j).carrier)
        (PadicAlgCl ℓ) i) x
    refine ⟨c.toLinearEquiv.toLinearMap.comp (e.toLinearMap.comp inc),
      c.toLinearEquiv.injective.comp (e.injective.comp leftInv.injective), fun x ↦ ?_⟩
    have eqv := (congrArg e (DirectSum.lmap_lof (fun j ↦ (T j).frobeniusEnd) i x).symm).trans
      (hf (inc x))
    exact (congrArg c.toLinearEquiv eqv).trans (c.map_frobenius _)
  have slice := @fromSlice X' Y' P'
    ‹IsSeparated (X ↘ Spec (.of k))› ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    ‹QuasiCompact (X ↘ Spec (.of k))›
    ‹IsSeparated (Y ↘ Spec (.of k))› ‹LocallyOfFiniteType (Y ↘ Spec (.of k))›
    ‹QuasiCompact (Y ↘ Spec (.of k))›
    ‹IsSeparated (P ↘ Spec (.of k))› ‹LocallyOfFiniteType (P ↘ Spec (.of k))›
    ‹QuasiCompact (P ↘ Spec (.of k))› p' s' product
  have native : SummandProperty (k := k) (ℓ := ℓ) p s := slice
  obtain ⟨_, ⟨iso⟩⟩ := coeff
  exact native L M hL hM N iso a b

end WeilII
