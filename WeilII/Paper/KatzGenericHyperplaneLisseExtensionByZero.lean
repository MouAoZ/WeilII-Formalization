module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
import WeilConjectures.AlgebraicGeometry.ClosurePointDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.LisseDirectImageVerdierDuality
import WeilII.AlgebraicGeometry.QuasiFiniteShriekClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilII.AlgebraicGeometry.QuasiFiniteAffineCompactVanishing
import WeilII.Paper.KatzGenericHyperplaneCohomologyComparison
import WeilII.Paper.ProjectiveHyperplaneFiberAffineComplement

/-!
# Generic hyperplane vanishing for a lisse sheaf

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.4–A.5,
pp. 220–221. Applying A.5 to the perverse sheaf `L[d]` on a smooth source of pure
dimension `d` gives a statement about ordinary cohomology of the unshifted sheaf.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Katz, Corollary A.5, pp. 220–221, specialized to a lisse sheaf on a smooth separated
scheme of finite type and pure dimension `d`. The homogeneous coordinate set `I` indexes a
basis and its dual. For every hyperplane in one dense open of the dual projective space,
extension by zero from the complement of its inverse image has zero cohomology below `d`.

Proof. Write `P` for projective space. The morphism `f` is separated of finite type by its
graph factorization over the field. The lisse sheaf `L` is constructible, so Katz A.4 gives
a dense open of hyperplanes on which the following comparison holds in every degree.
Fix such a hyperplane `H`. Put `B = P ∖ H`, `V = f⁻¹B`, and let `j : V ⟶ X` and `g : V ⟶ B`
be the inclusion and restriction. For `M = j^*L`, the comparison identifies
`Hʳ(X, j_! M)` with `H_cʳ(B, Rg_* M)`. The open subscheme `V` is smooth of relative dimension `d`,
the restriction `M` is lisse, and `g` is quasi-finite by base change. Verdier duality
identifies the linear dual of the latter group with `H^{2d-r}(B, Rg_! T)`, where
`T = M^∨(d)` is lisse.

The incidence equation of `H` is a section of the twisting line. Its nonvanishing locus
`B` is affine, since the coordinate sections of that line have affine nonvanishing loci
covering projective space. Let `Z` be the reduced closure of the image of `g` in `B`.
It is affine. By quasi-compactness every point of `Z` specializes from an image point.
Each image point closure has dimension bounded by its source point closure, so
`dim Z ≤ dim V ≤ d`. The closed-support comparison for its exceptional direct image gives a
constructible sheaf `A` on `Z` with `Hᵐ(B, Rg_! T) ≅ Hᵐ(Z, A)`. For `r < d` we have
`2d-r > d`, and the affine cohomological dimension bound kills this group. Linear duals
over a field detect zero, so the original cohomology group vanishes. -/
public theorem exists_denseOpen_isZero_lisse_hyperplaneExtensionByZero
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (I : Type u) [Fintype I] [Nontrivial I] (d : ℕ) {X : Scheme.{u}} :
    let k := AlgebraicClosure k₀
    let S := Spec (CommRingCat.of k)
    let P := ℙ(I; S)
    letI : S.Over S := ⟨𝟙 S⟩
    ∀ [X.Over S] [SmoothOfRelativeDimension d (X ↘ S)] [IsSeparated (X ↘ S)]
      [QuasiCompact (X ↘ S)] (f : X ⟶ P) [f.IsOver S] [LocallyQuasiFinite f]
      (L : ProEtale.AdicSheaf ℓ X), ProEtale.IsAdicLisseSheaf L →
      ∃ W : P.Opens, Dense (W : Set P) ∧
        ∀ (H : S ⟶ P) [H.IsOver S], H (IsLocalRing.closedPoint k) ∈ W →
          let j := ((projectiveHyperplaneFiber H).comap f).subschemeι.openComplement.ι
          let M := (ProEtale.adicUpperStar ℓ j).obj L
          let F := (ProEtale.adicOpenImmersionLowerShriek ℓ j).obj M
          ∀ r : ℤ, r < (d : ℤ) → IsZero ((ProEtale.algClosedCohomology ℓ (X ↘ S) r).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  intro k S P hXS hs hsep hqc f hf hfq L hL
  let π := P ↘ S
  have hcomp : f ≫ π = X ↘ S := comp_over f S
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth d _
  have : IsSeparated (f ≫ π) := hcomp ▸ hsep
  have : LocallyOfFiniteType (f ≫ π) := by rw [hcomp]; infer_instance
  have : QuasiCompact (f ≫ π) := hcomp ▸ hqc
  have : IsSeparated f := IsSeparated.of_comp f π
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f π
  have : QuasiCompact f := QuasiCompact.of_comp f π
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ S)
  have : IsNoetherian P := isNoetherian_of_locallyOfFiniteType π
  obtain ⟨compare, generic⟩ := exists_denseOpen_isIso_hyperplaneCohomologyComparison k₀ ℓ I f
  let hK := hL.isAdicConstructibleSheaf
  obtain ⟨W, hW, isoOn⟩ := generic L hK
  refine ⟨W, hW, ?_⟩
  intro H hH hHW
  let B := (projectiveHyperplaneFiber H).subschemeι.openComplement
  let j := (f ⁻¹ᵁ B).ι
  let g := morphismRestrict f B
  let a := B.ι ≫ π
  have hpre : ((projectiveHyperplaneFiber H).comap f).subschemeι.openComplement = f ⁻¹ᵁ B := by
    ext x
    change x ∉ Set.range _ ↔ f x ∉ Set.range _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_comap]
    rfl
  rw [hpre]
  dsimp only
  intro r hr
  have : IsAffine B.toScheme := isAffineOpen_projectiveHyperplaneFiber_complement k I H
  have : LocallyQuasiFinite g := inferInstanceAs (LocallyQuasiFinite (f ∣_ B))
  have hga : g ≫ a = j ≫ (X ↘ S) := by
    change (f ∣_ B) ≫ B.ι ≫ π = _
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hcomp]
  have : SmoothOfRelativeDimension d (g ≫ a) := by
    rw [hga]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d j (X ↘ S)
  have : IsSeparated (g ≫ a) := by rw [hga]; infer_instance
  have : QuasiCompact (g ≫ a) := by rw [hga]; infer_instance
  let M := (ProEtale.adicUpperStar ℓ j).obj L
  have hC := isZero_compactCohomology_quasiFinite_lisse_of_affine k₀ ℓ a g d M (hL.upperStar j) r hr
  have := isoOn H hHW r
  exact hC.of_iso (asIso ((compare H r).app ⟨L, hK⟩)).symm

end WeilII
