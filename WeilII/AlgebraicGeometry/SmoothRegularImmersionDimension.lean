module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- A smooth regular closed subscheme of codimension `c` in a smooth scheme of pure
dimension `n` over a perfect field is smooth of pure dimension `n - c`. Zhang, §2,
uses the case of a smooth hypersurface in affine space before Lemma 2.1. Around each
point of the subscheme the local dimensions differ by `c`, by the regular sequence
calculation in `IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension`.
The ambient open is nonempty, so its relative dimension is uniquely `n`. These
neighborhoods cover the subscheme. -/
public theorem smoothOfRelativeDimension_of_regularImmersion
    {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} (c n : ℕ)
    (i : Y ⟶ X) [IsRegularImmersion c i] (a : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension n a] [Smooth (i ≫ a)] :
    SmoothOfRelativeDimension (n - c) (i ≫ a) := by
  have := SmoothOfRelativeDimension.smooth n a
  apply smoothOfRelativeDimension_of_forall_exists_mem
  intro y
  obtain ⟨W, _, hy, p, d, hdp, hp, hd⟩ :=
    IsRegularImmersion.exists_isAffineOpen_smoothOfRelativeDimension c i a
      (Smooth.isRegularLocalRing_stalk (i ≫ a)) y
  have : Nonempty W.toScheme := ⟨⟨i y, hy⟩⟩
  have hn : SmoothOfRelativeDimension n (W.ι ≫ a) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n W.ι a
  have := SmoothOfRelativeDimension.eq_of_field _ hp hn
  exact ⟨i ⁻¹ᵁ W, hy, (show d = n - c by omega) ▸ hd⟩

end WeilII
