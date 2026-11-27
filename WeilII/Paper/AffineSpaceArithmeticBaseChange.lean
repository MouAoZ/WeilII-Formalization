module
public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
public import WeilII.AlgebraicGeometry.WeilPresentationPullback

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace WeilII
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] (I : Type u)
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "𝓧" => 𝔸(I; Spec (CommRingCat.of k))
local notation "𝓩" => 𝔸(I; Spec (CommRingCat.of K))
local notation "i" => Iso.hom (affineSpaceBaseChangeFieldIso k K I)

/-- The first projection in the affine-space base-change square is the coordinate map. -/
theorem affineSpaceBaseChangeFieldIso_hom_fst : i ≫ Limits.pullback.fst (𝓧 ↘ Spec (CommRingCat.of k)) g = AffineSpace.map I g :=
  (AffineSpace.isPullback_map (n := I) g).isoPullback_hom_fst

variable [Finite k] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
variable (E : ProEtale.AdicSheaf ℓ 𝔸(I; Spec (CommRingCat.of k))) (hE : ProEtale.IsAdicLisseSheaf E)

/-- In geometric coordinates the pullback of the restricted Weil sheaf is the canonical
Weil sheaf of the arithmetic pullback. -/
theorem affineSpaceArithmeticPullback_iso : Nonempty ((WeilSheaf.upperStar i).obj
    ((WeilSheaf.baseChangeField K).obj (WeilSheaf.geometricFiberPullback (k₀ := k) hE)) ≅
    WeilSheaf.geometricFiberPullback (k₀ := K) (ProEtale.IsAdicLisseSheaf.upperStar (AffineSpace.map I g) hE)) :=
  AdicInvariantPresentation.arithmeticBaseChange (k := k) (X := 𝓧) K (Z := 𝓩) i (AffineSpace.map I g)
    (affineSpaceBaseChangeFieldIso_hom_fst (k := k) (K := K) I) hE

/-- Arithmetic base change for a lisse sheaf on affine space of any coordinate type. -/
theorem affineSpaceArithmeticBaseChange_iso : Nonempty (affineSpaceWeilSheafBaseChangeField K
    (WeilSheaf.geometricFiberPullback (k₀ := k) hE) ≅
    WeilSheaf.geometricFiberPullback (k₀ := K) (ProEtale.IsAdicLisseSheaf.upperStar (AffineSpace.map I g) hE)) :=
  affineSpaceArithmeticPullback_iso (K := K) I E hE

end WeilII
