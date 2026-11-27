module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Direct sums of maps with prescribed basis images -/

public section

open DirectSum Module

namespace WeilII

/-- A family of linear maps exhibits its target as a direct sum when its values on the
chosen bases, indexed summand by summand, form a basis of the target. -/
theorem exists_directSumEquiv_of_basisImages {K : Type*} [CommSemiring K]
    {S : Type*} [DecidableEq S] {J : S → Type*} {M : S → Type*}
    [∀ s, AddCommMonoid (M s)] [∀ s, Module K (M s)]
    {N : Type*} [AddCommMonoid N] [Module K N]
    (b : ∀ s, Basis (J s) K (M s)) (t : Basis (Σ s, J s) K N)
    (f : ∀ s, M s →ₗ[K] N) (hf : ∀ s j, f s (b s j) = t ⟨s, j⟩) :
    ∃ e : (⨁ s, M s) ≃ₗ[K] N, ∀ s x, e (lof K S M s x) = f s x := by
  let F := toModule K S N f
  let G := t.constr K (fun i ↦ lof K S M i.1 (b i.1 i.2))
  have hG (i : Σ s, J s) : G (t i) = lof K S M i.1 (b i.1 i.2) := t.constr_basis _ _ i
  have hFG : F.comp G = LinearMap.id := by
    apply t.ext
    intro i
    rw [LinearMap.comp_apply, hG, toModule_lof, hf, LinearMap.id_apply]
  have hGF : G.comp F = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro s
    apply (b s).ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.id_apply, F, toModule_lof, hf, hG]
  exact ⟨LinearEquiv.ofLinearMap F G hFG hGF, fun s x ↦ toModule_lof _ _ _⟩

end WeilII
