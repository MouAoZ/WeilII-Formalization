module

public import WeilConjectures.WeilSheaf.Cohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.WeilSheaf.LissePoincarePairing
import WeilII.AlgebraicGeometry.AffineAdicCohomologicalDimension
import WeilII.AlgebraicGeometry.WeilSheafOrdinaryCohomologyGeometricComparison

/-!
# Compactly supported cohomology below the dimension of a smooth affine scheme

Zhang, *On an elementary proof of Weil II*, §2, p. 2, uses this vanishing to obtain the
initial injection in (†) for a smooth affine hypersurface.
-/

open AlgebraicGeometry

namespace WeilII

universe u

/-- On a smooth affine scheme of pure dimension `d` over a finite field, the geometric
compactly supported cohomology of a lisse Weil sheaf vanishes in every degree `r < d`.

Proof. Write `Z̄` for the base change to the algebraic closure. It is affine and of finite
type, and base change preserves smoothness of relative dimension `d`, so its Krull
dimension is at most `d`. Set `t = 2d - r`. The dual of `L` is locally the dual of a
finite free sheaf, so its geometric carrier is lisse and constructible. Since `t > d`,
Artin's affine vanishing theorem in its constructible ℓ-adic form gives zero ordinary
cohomology for this carrier in degree `t`. The comparison with geometric cohomology
identifies this zero space with the carrier of the ordinary Weil cohomology of the dual.

Since `r + t = 2d`, Poincaré duality pairs this space perfectly with the compactly
supported cohomology of `L` in degree `r`, with values in the Tate line of twist `-d`.
Every vector in the latter cohomology pairs to zero against the entire ordinary
cohomology space. Injectivity into its linear dual forces the vector to be zero.

Zhang cites SGA 4, Exposé XIV, Théorème 3.1 after (†) on p. 2. The pairing with the Tate
twist on the value line is given in `WeilSheaf/LissePoincarePairing.lean`. -/
public theorem subsingleton_compactlySupportedCohomology_of_lt_dimension
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] [IsAffine Z]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))] (d : ℕ)
    [SmoothOfRelativeDimension d (Z ↘ Spec (CommRingCat.of k))]
    (L : WeilSheaf k ℓ Z) (hL : L.IsLisse) {r : ℤ} (hr : r < (d : ℤ)) :
    Subsingleton (L.compactlySupportedCohomology r).carrier := by
  let a := Z ↘ Spec (CommRingCat.of k)
  have : SmoothOfRelativeDimension d a.geometricFiberToAlgebraicClosure :=
    smoothOfRelativeDimension_pullback_snd d a (Scheme.specAlgebraicClosure k).hom
  have : IsAffineHom a.geometricFiberToAlgebraicClosure :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback a (Scheme.specAlgebraicClosure k).hom) inferInstance
  have : IsAffine a.geometricFiber := isAffine_of_isAffineHom a.geometricFiberToAlgebraicClosure
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension a.geometricFiberToAlgebraicClosure d
  let t := 2 * (d : ℤ) - r
  let M := L.dual hL
  have hz := isZero_algClosedCohomology_of_isAffine k ℓ a.geometricFiberToAlgebraicClosure
    M.carrier M.isAdicConstructibleSheaf_carrier d
    (lt_of_le_of_lt hdim (by norm_cast; omega)) t (by dsimp [t]; omega)
  obtain ⟨e⟩ := nonempty_cohomologyCarrier_linearEquiv_algClosedCohomology M t
  have : Subsingleton (M.cohomology t).carrier := e.toEquiv.subsingleton_congr.mpr
    (ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat ℓ).map_isZero hz))
  obtain ⟨P, hP, _⟩ := WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual_mul
    d L hL r t (by dsimp [t]; omega)
  exact P.toPerfPair.toEquiv.subsingleton_congr.mpr inferInstance

end WeilII
