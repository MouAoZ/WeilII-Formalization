module

public import WeilConjectures.PoincareDuality.CompactSupportKunneth
import WeilII.CategoryTheory.KunnethComparison

/-! # Naturality of the inverse compact-support Künneth isomorphism in both coefficients -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The inverse Künneth map for a cartesian square is natural for arbitrary coefficient
morphisms on both factors. In the inverse factorization of
`PoincareDuality/CompactSupportKunneth.lean`, pass the coefficient maps through the outer
projection, base change, the two braidings and the inner projection, and the inverse
composition comparison. Equivalently this is categorical pasting for identity pullbacks. -/
public theorem compactSupportKunneth_inv_naturality
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]
    {P X Y S : Over (Spec (.of Ω))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    {p : P ⟶ X} {s : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (sq : IsPullback s p g f)
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : K ⟶ K') (y : L ⟶ L') :
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) P).toMonoidalCategoryStruct
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) S).toMonoidalCategoryStruct
    let ps := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p
    let ss := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s
    let h := boundedConstructibleLowerShriek ℓ (p ≫ f)
    (compactSupportKunnethIso ℓ sq K L).inv ≫ h.map (ps.map x ⊗ₘ ss.map y) =
      ((boundedConstructibleLowerShriek ℓ f).map x ⊗ₘ (boundedConstructibleLowerShriek ℓ g).map y) ≫
        (compactSupportKunnethIso ℓ sq K' L').inv := by
  intro ps ss h
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) P
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) X
  let := monoidalCategory_boundedConstructible (ℓ := ℓ) S
  let := boundedConstructibleBraiding (ℓ := ℓ) P
  let := boundedConstructibleBraiding (ℓ := ℓ) X
  let assemble := KunnethComparison.paste (boundedConstructibleLowerShriek ℓ p)
    (boundedConstructibleLowerShriek ℓ f) (boundedConstructibleLowerShriek ℓ g) h ps ss
    (boundedConstructibleUpperStar _ ℓ f)
    (boundedConstructibleExceptionalProjection ℓ p) (boundedConstructibleExceptionalProjection ℓ f)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ p f)
    (fun A B ↦ (compactSupportKunnethIso ℓ sq A B).inv) (fun _ _ ↦ rfl)
  have natural := assemble (𝟭 _) (𝟭 _) (𝟭 _) (𝟭 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _)
    (by intro A B; simp) (by intro A B; simp)
    (by intro B; simp) (by intro N; simp)
    (by intro A B; simp) (by intro A B; simp) K L _ _ rfl rfl
  exact natural.2 x y

end WeilII
