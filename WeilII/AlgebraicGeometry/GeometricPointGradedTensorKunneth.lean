module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TraceFormula.PointTrace
import WeilII.AlgebraicGeometry.GeometricPointGradedBasis
import WeilII.AlgebraicGeometry.GeometricPointGradedTensorPairing
import WeilII.LinearAlgebra.DirectSumBasisEquivalence
import WeilII.CategoryTheory.TensorProductBiproductPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # The graded Künneth isomorphism at a geometric point

Zhang uses the compact-support Künneth formula on p. 2 to deduce Theorem 1.1 from
Proposition 1.5. This is its graded tensor calculation on the base point, using the
shifted-unit description of cohomology in `WeilConjectures.TraceFormula.PointTrace`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory MonoidalCategory DirectSum
open scoped CategoryTheory.Obj TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 10
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]

/-- Split the unit in total degree `d = a + b` into the ordered tensor of the units in
degrees `a` and `b`. Its inverse combines the shifts by `boundedConstructibleShiftTensorShiftIso`
from `TraceFormula.DualizableShift` and applies the shifted left unitor.
On the single-complex representatives it sends the generator to `1 ⊗ 1`. -/
def geometricPointShiftedUnitTensorIso {a b d : ℤ} (h : a + b = d) :
    shiftedUnit ℓ Ω (-d) ≅ shiftedUnit ℓ Ω (-a) ⊗ shiftedUnit ℓ Ω (-b) :=
  letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) (point Ω)).toMonoidalCategoryStruct
  let U := 𝟙_ (Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  let Λ := Profinite.padicAlgClRingObj ℓ
  let ι := (boundedConstructible (condensedRingObj Λ (point Ω).left)).ι
  let combine := boundedConstructibleShiftTensorShiftIso ℓ (point Ω) U U (-a) (-b) ≪≫
    (shiftFunctor _ (-a + -b)).mapIso (λ_ U) ≪≫
    eqToIso (congrArg (fun i : ℤ ↦ (shiftFunctor _ i).obj U) (show -a + -b = -d by lia))
  ((((ι.commShiftIso (-a)).app U) ⊗ᵢ ((ι.commShiftIso (-b)).app U)).symm ≪≫
    ι.mapIso combine ≪≫ (ι.commShiftIso (-d)).app U).symm

set_option maxHeartbeats 1800000 in
/-- For bounded constructible complexes on a separably closed point, tensoring shifted-unit
morphisms gives a linear equivalence from the direct sum of the bidegrees of total degree
`d` to degree `d` of the derived tensor product. Zhang uses Künneth on p. 2.
The point decomposition and Hom computations come from `WeilConjectures.TraceFormula.PointTrace`.

Proof. Write `Uᵢ = 𝟙[-i]`. The unit and its shifts are K-flat since tensoring with
them is isomorphic to a shift and hence preserves acyclic complexes. The derived shift
comparison is therefore computed on their single-complex representatives. It moves the
left shift out first, with sign +1. The right shift then sees the unshifted left unit in
degree zero, so its sign is also +1. The inverse shifted left unitor and inverse tensor
shift therefore take the generator of `U_d` to the ordered tensor of generators.
Precomposition with the shifted scalar endomorphism of the unit is the scalar action on
each Hom space. Naturality of the left and right unitors, their agreement on the unit,
and naturality of the tensor shifts move a scalar on either input to this same scalar on
`U_d`. Thus tensoring morphisms after splitting the unit is bilinear. Extend it by the
tensor product universal property on each bidegree and then by the direct sum universal property.

Choose finite shifted-unit decompositions of both complexes. A morphism from `U_a` to the
first complex is determined by its projections onto the summands. Each projection of
degree different from `a` is zero, and each of degree `a` is a unique scalar times the
identity. The sum of inclusions times projections is the identity, so the inclusions in
degree `a` form a basis. The same argument applies to the second complex in degree `b`.
Tensor the inclusions and projections in ordered pairs, identifying each tensor of units
with the unit of their total degree by the displayed shift isomorphism. Their composites
are identities on matching pairs and zero on different pairs. Bilinearity of tensor on
morphisms makes the sum of the corresponding projectors the identity on the tensor product.
Hence the paired inclusions of total degree `d` give a basis of the target by the same
projection argument. The tensor product bases in the summands of the source give a basis
of the direct sum indexed by exactly these ordered pairs. The linear map takes each source
basis vector to the corresponding target basis vector and is therefore an equivalence. -/
theorem geometricPointGradedTensorKunneth [IsSepClosed Ω]
    (A B : Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧) (d : ℤ) :
    ∃ e : (⨁ s : {p : ℤ × ℤ // p.1 + p.2 = d},
        ((gradedHom ℓ Ω (-s.1.1)).obj A.obj) ⊗[PadicAlgCl ℓ]
          ((gradedHom ℓ Ω (-s.1.2)).obj B.obj)) ≃ₗ[PadicAlgCl ℓ]
        (gradedHom ℓ Ω (-d)).obj (A.obj ⊗ B.obj),
      ∀ (s : {p : ℤ × ℤ // p.1 + p.2 = d})
        (x : (gradedHom ℓ Ω (-s.1.1)).obj A.obj) (y : (gradedHom ℓ Ω (-s.1.2)).obj B.obj),
        gradedHomHom ℓ Ω (e (DirectSum.lof (PadicAlgCl ℓ) _ _ s (x ⊗ₜ[PadicAlgCl ℓ] y))) =
          (geometricPointShiftedUnitTensorIso ℓ Ω s.2).hom ≫
            (gradedHomHom ℓ Ω x ⊗ₘ gradedHomHom ℓ Ω y) := by
  classical
  let C := Dᵇc((point Ω).left)⟦Profinite.padicAlgClRingObj ℓ⟧
  let I := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point Ω).left)).ι
  let D (P : C) := (nonempty_shiftDecomposition_point ℓ Ω P).some.map I
  let r (P : C) (i : (D P).ι) := -(D P).deg i
  let u (P : C) (i : (D P).ι) : shiftedUnit ℓ Ω (-r P i) ≅ shiftedUnit ℓ Ω ((D P).deg i) :=
    eqToIso (congrArg (shiftedUnit ℓ Ω) (neg_neg _))
  let inc (P : C) (i : (D P).ι) := (u P i).hom ≫ (D P).incl i
  let pr (P : C) (i : (D P).ι) := (D P).proj i ≫ (u P i).inv
  have total (P : C) : ∑ i, pr P i ≫ inc P i = 𝟙 (I.obj P) := by
    simp only [pr, inc, Category.assoc, Iso.inv_hom_id_assoc]
    exact (D P).total
  have diag (P : C) (i : (D P).ι) : inc P i ≫ pr P i = 𝟙 _ := by
    simp only [inc, pr, Category.assoc, reassoc_of% (D P).incl_proj_self i, Iso.hom_inv_id]
  have off (P : C) (i j : (D P).ι) (h : i ≠ j) : inc P i ≫ pr P j = 0 := by
    simp only [inc, pr, Category.assoc, reassoc_of% (D P).incl_proj_of_ne i j h,
      Limits.zero_comp, Limits.comp_zero]
  have basisA := exists_geometricPointGradedBasis ℓ Ω (r A) A.obj
    (inc A) (pr A) (total A) (diag A) (off A)
  let bA := basisA.choose
  have hA := basisA.choose_spec
  have basisB := exists_geometricPointGradedBasis ℓ Ω (r B) B.obj
    (inc B) (pr B) (total B) (diag B) (off B)
  let bB := basisB.choose
  have hB := basisB.choose_spec
  let J := (D A).ι × (D B).ι
  let deg (p : J) := r A p.1 + r B p.2
  let split (p : J) := geometricPointShiftedUnitTensorIso ℓ Ω (a := r A p.1) (b := r B p.2) rfl
  let incl (p : J) := (split p).hom ≫ (inc A p.1 ⊗ₘ inc B p.2)
  let proj (p : J) := (pr A p.1 ⊗ₘ pr B p.2) ≫ (split p).inv
  have comm := isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point Ω).left
  let : MonoidalClosed (PointMod ℓ Ω) := @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ comm
  let : SymmetricCategory (PointMod ℓ Ω) := @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ comm
  have : MonoidalPreadditive (DerivedCategory (PointMod ℓ Ω)) :=
    DerivedCategory.monoidalPreadditive (A := PointMod ℓ Ω)
  have presentation := tensorProduct_biproductPresentation
    (inc A) (pr A) (inc B) (pr B) (total A) (total B) (diag A) (diag B) (off A) (off B) split
  have basisT := exists_geometricPointGradedBasis ℓ Ω deg (A.obj ⊗ B.obj)
    incl proj presentation.1 presentation.2.1 presentation.2.2
  let bT := basisT.choose
  have hT := basisT.choose_spec
  let S := {p : ℤ × ℤ // p.1 + p.2 = d}
  let K (s : S) := {i // r A i = s.1.1} × {j // r B j = s.1.2}
  let regroup : (Σ s, K s) ≃ {p : J // deg p = d} :=
    { toFun := fun ⟨s, i, j⟩ ↦ ⟨(i.1, j.1), by dsimp [deg]; rw [i.2, j.2, s.2]⟩
      invFun := fun ⟨p, hp⟩ ↦ ⟨⟨(r A p.1, r B p.2), hp⟩, ⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩
      left_inv := by rintro ⟨⟨⟨a,b⟩,h⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩; dsimp at hi hj; subst a; subst b; rfl
      right_inv := fun _ ↦ rfl }
  choose β hβ using fun s : S ↦ exists_geometricPointGradedTensorPairing ℓ Ω A.obj B.obj
    s.1.1 s.1.2 d s.2 (geometricPointShiftedUnitTensorIso ℓ Ω s.2).hom
  have equiv := exists_directSumEquiv_of_basisImages (J := K)
    (fun s : S ↦ (bA s.1.1).tensorProduct (bB s.1.2)) ((bT d).reindex regroup.symm)
    (fun s ↦ TensorProduct.lift (β s)) (by
      rintro ⟨⟨a,b⟩,hs⟩ ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      dsimp at hi hj hs
      subst a; subst b; subst d
      let s : {p : ℤ × ℤ // p.1 + p.2 = r A i + r B j} := ⟨(r A i, r B j), rfl⟩
      let ij : {k // r A k = r A i} × {k // r B k = r B j} := (⟨i, rfl⟩, ⟨j, rfl⟩)
      calc
        _ = β s (bA _ ij.1) (bB _ ij.2) :=
          congrArg (TensorProduct.lift (β s)) (Module.Basis.tensorProduct_apply _ _ _ _)
        _ = bT (deg (i,j)) ⟨(i,j), rfl⟩ := by
          change gradedHomHom ℓ Ω (β s _ _) = gradedHomHom ℓ Ω (bT _ _)
          rw [hβ, hA, hB]
          exact (hT (i, j)).symm
        _ = _ := ((bT (deg (i, j))).reindex_apply regroup.symm ⟨s, ij⟩).symm)
  refine ⟨equiv.choose, fun s x y ↦ ?_⟩
  rw [equiv.choose_spec, TensorProduct.lift.tmul, hβ]

end WeilII
