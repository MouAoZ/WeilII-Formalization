module

public import WeilII.AlgebraicGeometry.ShriekTriangleFieldStructures
import WeilII.AlgebraicGeometry.CompactificationComparisonNatIso
meta import WeilConjectures.Tactic.ExactByKernel

/-! # The lower-shriek composition isomorphism under a change of field structure -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {a : X.left ⟶ Spec (.of k)} {b : Y.left ⟶ Spec (.of k)} {c : Z.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    [LocallyOfFiniteType (Over.mk c).hom] [QuasiCompact (Over.mk c).hom] [IsSeparated (Over.mk c).hom]
    (wf : f.left ≫ b = a) (wg : g.left ≫ c = b)

local notation "f₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf
local notation "g₁" => Over.homMk (U := Over.mk b) (V := Over.mk c) g.left wg
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- Changing the structure maps of a composable pair preserves its lower-shriek compositor.
Compute both sides on the same triangle using the arbitrary-triangle theorem. Identify the
three outer compactification comparisons and the isomorphism of the fixed triangle. -/
public theorem shriekCompositionIso_changeStructure :
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ f₁ g₁ =
      boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g := by
  let T := chosenTriangle f g
  have wfg : (f ≫ g).left ≫ c = a := by
    change (f.left ≫ g.left) ≫ c = a
    rw [Category.assoc, wg, wf]
  have hf := compactificationComparisonIso_changeStructure ℓ f wf T.cf (compactificationOverField f)
  have hg := compactificationComparisonIso_changeStructure ℓ g wg T.cg (compactificationOverField g)
  have hfg := compactificationComparisonIso_changeStructure ℓ (f ≫ g) wfg
    (compactificationOverField (f ≫ g)) T.cfg
  have hT := triangleComposition_changeStructure ℓ f g wf wg T
  let F := boundedConstructibleLowerShriek ℓ f
  let G := boundedConstructibleLowerShriek ℓ g
  let H := boundedConstructibleLowerShriek ℓ (f ≫ g)
  let P := boundedConstructibleLowerShriekOfCompactification ℓ (f := f) T.cf
  let Q := boundedConstructibleLowerShriekOfCompactification ℓ (f := g) T.cg
  let R := boundedConstructibleLowerShriekOfCompactification ℓ (f := f ≫ g) T.cfg
  let j (f' : P ≅ F) (g' : Q ≅ G) := NatTrans.hcomp f'.hom g'.hom
  let assemble (e : H ≅ R) (t : P ⋙ Q ≅ R) (u : P ⋙ Q ⟶ F ⋙ G) := e.hom ≫ t.inv ≫ u
  let i₁ : P ≅ F := by exact_by_kernel (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
    (f := f₁) T.cf (compactificationOverField f₁))
  let i₀ : P ≅ F :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (f := f) T.cf (compactificationOverField f)
  let j₁ : Q ≅ G := by exact_by_kernel (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
    (f := g₁) T.cg (compactificationOverField g₁))
  let j₀ : Q ≅ G :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (f := g) T.cg (compactificationOverField g)
  let k₁ : H ≅ R := by exact_by_kernel (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
    (f := f₁ ≫ g₁) (compactificationOverField (f₁ ≫ g₁)) T.cfg)
  let k₀ : H ≅ R :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (f := f ≫ g) (compactificationOverField (f ≫ g)) T.cfg
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := f) (g := g) T
  have := isIso_exchange_triangleShriekTriangle ℓ (f := f) (g := g) T
  have := isIso_baseChange_triangleShriekTriangle ℓ (f := f₁) (g := g₁) T
  have := isIso_exchange_triangleShriekTriangle ℓ (f := f₁) (g := g₁) T
  let t₁ : P ⋙ Q ≅ R := by exact_by_kernel ((𝔽).compIso (triangleShriekTriangle (f := f₁) (g := g₁) T))
  let t₀ : P ⋙ Q ≅ R := (𝔽).compIso (triangleShriekTriangle (f := f) (g := g) T)
  have hi : i₁ = i₀ := by exact_by_kernel hf
  have hj : j₁ = j₀ := by exact_by_kernel hg
  have hk : k₁ = k₀ := by exact_by_kernel hfg
  have ht : t₁ = t₀ := by exact_by_kernel hT
  have comp : assemble k₁ t₁ (j i₁ j₁) = assemble k₀ t₀ (j i₀ j₀) := by rw [hi, hj, hk, ht]
  apply Iso.ext
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f₁ g₁ T,
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f g T]
  exact_by_kernel comp

end WeilII
