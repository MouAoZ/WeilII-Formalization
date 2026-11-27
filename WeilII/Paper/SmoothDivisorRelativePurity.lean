module

public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.VerdierDualLocalization
import WeilII.AlgebraicGeometry.LisseClosedPurityOfConstant
import WeilII.AlgebraicGeometry.SmoothClosedConstantOrientation
import WeilII.AlgebraicGeometry.SmoothRegularImmersionDimension

/-!
# Relative purity for a smooth affine hypersurface

Zhang, *On an elementary proof of Weil II*, §2, p. 2, uses the codimension-one
purity isomorphism of SGA 4, Exposé XVI, 3.7, 3.8 and 3.10(a), before (†).
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Relative purity for a smooth hypersurface in Zhang, §2, p. 2, before (†).
The isomorphisms in the Weil category are natural in every morphism of lisse sheaves.

Over the algebraic closure, SGA 4, XVI, 3.7 and 3.8 concentrate the local
cohomology of the constant coefficients ℤ/ℓᵐ in degree two. By 3.10(a) that sheaf
is the dual of the ℓᵐ-th roots of unity. The supported Kummer boundary of a local
equation gives the orientation. It respects coefficient reduction by naturality
of the Kummer boundary and commutes with geometric Frobenius by base change (3.8.1).

Compare the closed-support functor on the constant Weil complex with the derived
inverse limit of these finite complexes on the geometric pro-étale site, followed
by extension of scalars. The dual root lines have surjective transitions and their
derived limit is the integral dual Tate line in degree zero. Its Frobenius acts
through the inverse cyclotomic character. Thus the only cohomology sheaf of the
exceptional pullback is the Weil line of twist −1 in degree two. Good truncation
in the category of Weil sheaves identifies the complex with this line shifted by −2.

A lisse sheaf is dualizable. Applying the projection formula for its dual to the
closed direct image and taking adjoints moves the lisse factor across the exceptional
pullback as its ordinary restriction. Tensor the constant-coefficient orientation
with that restriction. Tensoring with a lisse factor commutes with shifts and agrees
in degree zero with the sheaf tensor product. The adjunctions and tensor maps are
natural, giving the displayed square for every coefficient morphism. -/
public theorem smoothDivisorRelativePurity
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {I : Type u} [Finite I] (_hdim : 2 ≤ Nat.card I)
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (i : Y ⟶ 𝔸(I; Spec (CommRingCat.of k))) [IsSmoothAffineHypersurface i]
    [i.IsOver (Spec (CommRingCat.of k))] :
    letI := isNoetherian_of_locallyOfFiniteType
      (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    let supported := WeilSheaf.toComplex ⋙ WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ)
      i i.openComplement.ι (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
    let pull := WeilSheaf.upperStar (k₀ := k) (l := ℓ) i
    let tate := WeilSheaf.tateTwistSheaf k ℓ Y (-1)
    let shifted := WeilSheaf.toComplex ⋙ shiftFunctor (WeilComplex k ℓ Y) (-2 : ℤ)
    ∃ e : ∀ (G : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))) (hG : G.IsLisse),
        supported.obj G ≅ shifted.obj ((pull.obj G).tensorObj tate (hG.upperStar i)),
      ∀ (G H : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))) (hG : G.IsLisse) (hH : H.IsLisse) (f : G ⟶ H),
        supported.map f ≫ (e H hH).hom =
          (e G hG).hom ≫ shifted.map
            (WeilSheaf.tensorHom (pull.map f) (𝟙 tate) (hG.upperStar i) (hH.upperStar i)) := by
  let a := 𝔸(I; Spec (.of k)) ↘ Spec (.of k)
  let d := Nat.card I - 1
  have hn : d + 1 = Nat.card I := by dsimp [d]; omega
  have : SmoothOfRelativeDimension (Nat.card I) a :=
    AffineSpace.smoothOfRelativeDimension_over I (Spec (.of k))
  have : SmoothOfRelativeDimension d (Y ↘ Spec (.of k)) := by
    rw [← comp_over i (Spec (.of k))]
    exact smoothOfRelativeDimension_of_regularImmersion 1 (Nat.card I) i a
  have : SmoothOfRelativeDimension (d+1) a := hn.symm ▸
    AffineSpace.smoothOfRelativeDimension_over I (Spec (.of k))
  exact lisseClosedPurityOfConstant i (WeilSheaf.tateTwistSheaf k ℓ Y (-1)) (-2)
    (smoothClosedConstantOrientation d i)

end WeilII
