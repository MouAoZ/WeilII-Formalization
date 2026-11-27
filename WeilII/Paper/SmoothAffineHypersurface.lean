module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

/-!
# Smooth hypersurfaces in affine space

Zhang, *On an Elementary Proof of Weil II*, §2, p. 2, uses a smooth hypersurface
in affine space and the open immersion of its complement in the sequence (†).
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- A smooth hypersurface as in Zhang, §2, p. 2. The closed immersion `i` is locally cut out
by a single non-zero-divisor, and its source is smooth over `k` via the affine-space projection.
The inherited closed immersion gives the complementary open immersion `i.openComplement.ι`. -/
public class IsSmoothAffineHypersurface {k : Type u} [Field k] {I : Type u} [Finite I]
    {Y : Scheme.{u}} (i : Y ⟶ 𝔸(I; Spec (CommRingCat.of k))) : Prop extends
    IsRegularImmersion 1 i, Smooth (i ≫ (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

end WeilII
