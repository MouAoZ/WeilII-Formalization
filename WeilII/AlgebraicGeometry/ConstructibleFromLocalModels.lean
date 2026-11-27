module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Checking constructibility on local models -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- An operation on module objects preserves constructibility if it commutes with pullback and
sends local models of locally finitely presented modules to finitely presented modules.
Use the stratification of the input and the specified cover on each stratum. -/
public theorem isConstructibleModuleObject_of_localModels
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (F : (X : Scheme.{u}) →
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) →
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (pull : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) P Q,
      ((f)^*⟦Λ⟧.obj P ≅ Q) → Nonempty ((f)^*⟦Λ⟧.obj (F X P) ≅ F Y Q))
    (localModels : ∀ (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] P,
      IsLocallyFinitelyPresented (condensedRingObj Λ X) P →
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i, ∃ Q,
        Nonempty ((𝒰.f i)^*⟦Λ⟧.obj P ≅ Q) ∧
        Mod.IsFinitelyPresented (condensedRingObj Λ (𝒰.X i)) (F (𝒰.X i) Q))
    {Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Z] (N)
    (hN : IsConstructibleModuleObject (condensedRingObj Λ Z) N) :
    IsConstructibleModuleObject (condensedRingObj Λ Z) (F Z N) := by
  obtain ⟨S, hS⟩ := hN
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff Λ (S.immersion a) _).2 ?_⟩
  have : TopologicalSpace.NoetherianSpace (S.domain a) := IsImmersion.noetherianSpace (S.immersion a)
  let P := (S.immersion a)^*⟦Λ⟧.obj N
  have hP := (isLocallyFinitelyPresented_mapMod_iff Λ (S.immersion a) N).1 (hS a)
  obtain ⟨𝒰, h𝒰⟩ := localModels (S.domain a) P hP
  obtain ⟨eS⟩ := pull (S.immersion a) N P (Iso.refl _)
  refine IsLocallyFinitelyPresented.of_iso eS.symm ((isLocallyFinitelyPresented_iff _).2
    ⟨𝒰, fun i ↦ ?_⟩)
  obtain ⟨Q, ⟨d⟩, hQ⟩ := h𝒰 i
  obtain ⟨e⟩ := pull (𝒰.f i) P Q d
  exact Mod.IsFinitelyPresented.of_iso e.symm hQ

end WeilII
