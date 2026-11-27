module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel

open CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

/-- The condensed principal quotient sequence is short exact when multiplication by the
generator is a topological embedding and the quotient is discrete. On a profinite test
object, a section in the kernel divides continuously by the generator, and maps to the
quotient lift continuously along any set-theoretic section. This is the sectionwise
argument of Bhatt–Scholze, §6.8, as in `PushResidueShortExact`. -/
public theorem shortExact_condensedPrincipalQuotient
    {R B : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (a : R) (ρ : R →+* B) (hc : Continuous ρ) (hs : Function.Surjective ρ)
    (hk : RingHom.ker ρ = Ideal.span {a}) (he : Topology.IsEmbedding (a * · : R → R)) :
    ∃ w : Profinite.continuousMapRingObjMulLeft.{u} R a ≫
        Profinite.continuousMapRingObjMap ρ hc = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  classical
  have ha : ρ a = 0 := by
    change a ∈ RingHom.ker ρ
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  let f := Profinite.continuousMapRingObjMulLeft.{u} R a
  let g := Profinite.continuousMapRingObjMap.{u} ρ hc
  have w : f ≫ g = 0 := by
    ext U x
    refine congrArg ULift.up (ContinuousMap.ext fun t ↦ ?_)
    change ρ (a * x.down t) = 0
    exact (map_mul ρ a _).trans (by rw [ha, zero_mul])
  let S := ShortComplex.mk f g w
  refine ⟨w, ?_⟩
  have hmono (U : Profinite.{u}ᵒᵖ) : Mono (((sheafToPresheaf _ _).map f).app U) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y h
    exact ULift.ext (ContinuousMap.ext fun t ↦ he.injective
      (congrArg (fun z : ULift.{u + 1} C(U.unop, R) ↦ z.down t) h))
  have surj (U : Profinite.{u}ᵒᵖ) : Function.Surjective (g.hom.app U) := by
    intro z
    refine ⟨ULift.up ⟨Function.surjInv hs ∘ z.down,
      continuous_of_discreteTopology.comp z.down.continuous⟩, ?_⟩
    exact ULift.ext (ContinuousMap.ext fun t ↦ Function.surjInv_eq hs _)
  have : Mono f := (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have cok : IsColimit (CokernelCofork.ofπ g w) := by
    apply Sheaf.isColimitCokernelCoforkOfSurjective f g w surj
    intro U z hz
    have hz' (t : U.unop) : z.down t ∈ Ideal.span {a} := by
      rw [← hk]
      exact congrArg (fun v : ULift.{u + 1} C(U.unop, B) ↦ v.down t) hz
    choose b hb using fun t ↦ Ideal.mem_span_singleton.mp (hz' t)
    have hb' : Continuous b := he.continuous_iff.2 (by
      change Continuous (fun t ↦ a * b t)
      exact (show (fun t ↦ a * b t) = z.down from funext fun t ↦ (hb t).symm) ▸ z.down.continuous)
    exact ⟨ULift.up ⟨b, hb'⟩, ULift.ext (ContinuousMap.ext fun t ↦ (hb t).symm)⟩

  have : Epi g := epi_of_isColimit_cofork cok
  exact ⟨S.exact_of_g_is_cokernel cok⟩

end WeilII
