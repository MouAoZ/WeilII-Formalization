module

public import Mathlib.AlgebraicGeometry.AffineSpace

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AffineSpace

namespace WeilII

universe u

/-- Splitting off the last coordinate of affine space over any base gives a pullback.
The equivalence permits the first block to use a different set of coordinate labels.
On a test scheme the unique lift appends its last global function to its first block. -/
public theorem affineSpaceLastCoordinatePullback (S : Scheme.{u}) {r : ℕ} {I : Type u}
    (e : I ≃ Fin r) :
    IsPullback
      (AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ ULift.up.{u} (Fin.last r)) S)
      (AffineSpace.reindex (fun i : I ↦ ULift.up.{u} (e i).castSucc) S)
      (𝔸(PUnit.{u + 1}; S) ↘ S) (𝔸(I; S) ↘ S) := by
  apply IsPullback.mk' (by simp)
  · intro T f g hlast hfirst
    apply hom_ext
    · simpa only [Category.assoc, reindex_over] using
        congrArg (fun h ↦ h ≫ 𝔸(I; S) ↘ S) hfirst
    · rintro ⟨j⟩
      induction j using Fin.lastCases with
      | last =>
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord]
          using congrArg (fun h ↦ h.appTop (coord S PUnit.unit)) hlast
      | cast i =>
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          Equiv.apply_symm_apply] using congrArg (fun h ↦ h.appTop (coord S (e.symm i))) hfirst
  · intro T a b comm
    let v (i : ULift.{u} (Fin (r + 1))) : Γ(T, ⊤) :=
      Fin.lastCases (a.appTop (coord S PUnit.unit)) (fun j ↦ b.appTop (coord S (e.symm j))) i.down
    refine ⟨homOfVector (a ≫ 𝔸(PUnit.{u + 1}; S) ↘ S) v, ?_, ?_⟩
    · apply hom_ext
      · simp
      · rintro ⟨⟩
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          homOfVector_appTop_coord]
        simp [v]
    · apply hom_ext
      · simpa only [Category.assoc, reindex_over, homOfVector_over] using comm
      · intro i
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
          homOfVector_appTop_coord]
        simp [v]

end WeilII
