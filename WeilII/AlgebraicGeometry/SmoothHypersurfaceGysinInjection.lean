module

public import WeilII.AlgebraicGeometry.SmoothHypersurfaceGysinSequence
import WeilII.AlgebraicGeometry.SmoothAffineLisseVanishing
import WeilII.AlgebraicGeometry.SmoothRegularImmersionDimension
import WeilConjectures.WeilSheaf.StalkTensorTrace

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The middle-degree injection in Zhang, §2, equation (†), p. 2. For a smooth
hypersurface in affine `n`-space, the source of the Gysin map into degree `n` is the
degree-`n-2` compactly supported cohomology of the restricted sheaf twisted by `-1`.
This sheaf is lisse on a smooth affine scheme of dimension `n-1`, so the source
vanishes. Exactness makes the restriction map injective, and the Gysin sequence
gives its Frobenius equivariance. -/
public theorem exists_injective_smoothHypersurfaceRestriction
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {n : ℕ} (hn : 2 ≤ n) {Y : Scheme.{u}}
    (i : Y ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) [IsSmoothAffineHypersurface i]
    (G : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) (hG : G.IsLisse) :
    letI := isNoetherian_of_locallyOfFiniteType
      (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    let V := G.compactlySupportedCohomology (n : ℤ)
    let W := WeilComplex.compactlySupportedCohomology
      (openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G) (n : ℤ)
    ∃ f : V.carrier →ₗ[PadicAlgCl ℓ] W.carrier,
      Function.Injective f ∧ Function.Semiconj f V.frobenius W.frobenius := by
  intro V W
  refine (fun (deduce : _ → _) ↦ deduce (smoothHypersurfaceGysinSequence i G hG)) ?_
  lift_lets -merge -underBinder
  intro a L j D η A B C res sequence
  let : Y.Over (Spec (CommRingCat.of k)) := ⟨i ≫ a⟩
  have : i.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ a))
  have : IsAffine Y := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hcard : Nat.card (ULift.{u} (Fin n)) = n := by simp
  have : SmoothOfRelativeDimension n a := by
    simpa only [hcard] using
      AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) (Spec (CommRingCat.of k))
  have : SmoothOfRelativeDimension (n - 1) (Y ↘ Spec (CommRingCat.of k)) :=
    smoothOfRelativeDimension_of_regularImmersion 1 n i a
  have hL : L.IsLisse := by
    dsimp only [L]
    apply WeilSheaf.IsLisse.tensorObj
    exact WeilSheaf.isLisse_tateTwistSheaf k ℓ Y (-1)
  have hr : (n : ℤ) - 2 < ((n - 1 : ℕ) : ℤ) := by omega
  have : Subsingleton (A (n : ℤ)).carrier :=
    subsingleton_compactlySupportedCohomology_of_lt_dimension (n - 1) L hL hr
  rw [show V = B (n : ℤ) by rfl, show W = C (n : ℤ) by rfl]
  refine ⟨res (n : ℤ), ?_⟩
  obtain ⟨gysin, δ, hex⟩ := sequence
  have h := hex (n : ℤ)
  exact ⟨(LinearMap.injective_iff_eq_zero_of_exact h.1).mpr (Subsingleton.elim _ _),
    h.2.2.2.2.1⟩

end WeilII
