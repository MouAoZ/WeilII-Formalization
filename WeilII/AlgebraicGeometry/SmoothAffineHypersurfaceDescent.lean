module

public import WeilII.Paper.SmoothAffineHypersurface
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Descent of smoothness for a principal hypersurface in affine space -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- A nonzero section on affine space cuts out a smooth hypersurface if its zero locus
is smooth after a field extension. This is the descent step in Zhang, Construction 2.5.
The two base-change squares for the affine space and the principal zero locus exhibit the
extended zero locus as the pullback over the field extension. Smoothness descends along
this faithfully flat quasi-compact cover. The original section is a non-zero-divisor in
the affine coordinate domain, so it generates the ideal as a weakly regular sequence of
length one. -/
public theorem isSmoothAffineHypersurface_of_smooth_fieldExtension
    {k K I : Type u} [Field k] [Field K] [Algebra k K] [Finite I]
    (s : Γ(𝔸(I; Spec (CommRingCat.of k)), ⊤)) (hs : s ≠ 0) :
    let T := Spec (CommRingCat.of K)
    let b := AffineSpace.map I (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    Smooth (𝔸(I; T).zeroLocusSubschemeι {b.appTop s} ≫ (𝔸(I; T) ↘ T)) →
      IsSmoothAffineHypersurface (𝔸(I; Spec (CommRingCat.of k)).zeroLocusSubschemeι {s}) := by
  intro T b h
  let S := Spec (CommRingCat.of k)
  let X := 𝔸(I; S)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hfs : Flat f ∧ Surjective f := (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have sq := (Scheme.isPullback_zeroLocusSubschemeι b {s} {b.appTop s}
    Set.image_singleton).paste_vert (AffineSpace.isPullback_map (n := I) f)
  have hsm : Smooth (X.zeroLocusSubschemeι {s} ≫ (X ↘ S)) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip
      ⟨⟨hfs.2, hfs.1⟩, inferInstance⟩ h
  let J : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {s})
  have hX : IsAffine X := isAffine_of_isAffineHom (X ↘ S)
  have hreg : IsRegularImmersion 1 J.subschemeι := by
    constructor
    intro x
    refine ⟨⟨⊤, isAffineOpen_top X⟩, trivial, [s], rfl, ?_, ?_⟩
    · exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
        (fun _ _ e ↦ mul_left_cancel₀ hs e)
    · rw [Ideal.ofList_singleton, J.ker_subschemeι]
      exact (Scheme.IdealSheafData.ideal_top_ofIdealTop _).symm
  exact { hreg with toSmooth := hsm }

end WeilII
