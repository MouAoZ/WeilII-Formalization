module

public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import WeilConjectures.WeilSheaf.SmoothPurityNativeProperTrace
public import WeilConjectures.WeilSheaf.SmoothPurityTraceUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.WeaklyEtale
import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber

/-! # Finite-base descent commutes with closed exceptional pullback -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.WeilComplex
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
variable {Z X : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]

/-- The exceptional pullback of any descended bounded constructible complex is the descent
of its finite-base exceptional pullback. Apply proper trace to the identity of the latter
object. Its adjunct is an isomorphism by weakly étale base change for the closed immersion
along the geometric projection. The trace and its adjunct are morphisms of Weil complexes.
Sources: `SmoothPurityNativeProperTrace` and `DualizingFieldChange/WeaklyEtale`. -/
public theorem closedSupportFiniteBaseDescent
    (N : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    letI : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
    letI : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    letI : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom := ‹QuasiCompact (X ↘ Spec (.of k))›
    letI : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom := ‹IsSeparated (X ↘ Spec (.of k))›
    letI : LocallyOfFiniteType (Over.mk (Z ↘ Spec (.of k))).hom := ‹LocallyOfFiniteType (Z ↘ Spec (.of k))›
    letI : QuasiCompact (Over.mk (Z ↘ Spec (.of k))).hom := ‹QuasiCompact (Z ↘ Spec (.of k))›
    letI : IsSeparated (Over.mk (Z ↘ Spec (.of k))).hom := ‹IsSeparated (Z ↘ Spec (.of k))›
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
    let j := i.openComplement.ι
    let hij := eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι
    let S := WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ) i j hij
    let P := (boundedConstructibleUpperShriek ℓ (properTraceBaseMap (k₀ := k) i)).obj N
    Nonempty (S.obj ((finiteBaseNativeDescent (k₀ := k)).obj N) ≅
      (finiteBaseNativeDescent (k₀ := k) (X := Z)).obj P) := by
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let : Fact (ringChar (AlgebraicClosure k)).Prime := ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  let : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) := ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := ℓ)⟩
  let : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  let : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  let : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom := ‹IsSeparated (X ↘ Spec (.of k))›
  let : LocallyOfFiniteType (Over.mk (Z ↘ Spec (.of k))).hom := ‹LocallyOfFiniteType (Z ↘ Spec (.of k))›
  let : QuasiCompact (Over.mk (Z ↘ Spec (.of k))).hom := ‹QuasiCompact (Z ↘ Spec (.of k))›
  let : IsSeparated (Over.mk (Z ↘ Spec (.of k))).hom := ‹IsSeparated (Z ↘ Spec (.of k))›
  let := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  intro j hij S P
  let f := properTraceBaseMap (k₀ := k) i
  let f' := geometricFiberOverMap f
  have : IsClosedImmersion f.left := ‹IsClosedImmersion i›
  have : IsClosedImmersion f'.left :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsClosedImmersion)
      i (comp_over i _) inferInstance
  let T := (finiteBaseNativeDescent (k₀ := k) (X := Z)).obj P
  let U := (finiteBaseNativeDescent (k₀ := k)).obj N
  let eT := (finiteBaseNativeDescentComparison (k₀ := k) (X := Z)).app P
  let eU := (finiteBaseNativeDescentComparison (k₀ := k)).app N
  let sq := (Scheme.Hom.isPullback_geometricFiberMap i (comp_over i (Spec (.of k)))).flip
  have hbc := isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale ℓ (i := f) (i' := f') sq N
  let adj := WeilComplex.closedUpperShriekAdjunction (k₀ := k) (l := ℓ) i j hij
  have := isIso_homEquiv_nativeProperTrace_of_isIso i (𝟙 P) T U eT eU hbc adj
  exact ⟨(asIso (adj.homEquiv T U (nativeProperTrace i (𝟙 P) T U eT eU))).symm⟩

end WeilII
