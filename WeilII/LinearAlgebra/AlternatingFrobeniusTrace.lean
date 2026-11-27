module

public import WeilConjectures.LinearAlgebra.TraceLongExactSequenceFinsum
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-! # Alternating Frobenius traces on a bounded long exact sequence

Source: the additivity step in Zhang's proof of Lemma 2.2. -/

namespace WeilII

universe u

/-- Frobenius power traces are additive on a bounded, equivariant long exact sequence.
Apply the linear alternating-trace formula to the powers of the three Frobenius maps.
Equivariance for a single Frobenius implies equivariance for each power. Source:
Zhang, proof of Lemma 2.2, and LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact. -/
public theorem alternatingTrace_eq_add_of_frobeniusExact
    {K : Type*} [Field K] (A B C : ℤ → FrobeniusModule.{u} K)
    (f : ∀ r, (A r).carrier →ₗ[K] (B r).carrier) (g : ∀ r, (B r).carrier →ₗ[K] (C r).carrier)
    (δ : ∀ r, (C r).carrier →ₗ[K] (A (r + 1)).carrier)
    (h : ∀ r, Function.Exact (f r) (g r) ∧ Function.Exact (g r) (δ r) ∧
      Function.Exact (δ r) (f (r + 1)) ∧
      Function.Semiconj (f r) (A r).frobenius (B r).frobenius ∧
      Function.Semiconj (g r) (B r).frobenius (C r).frobenius ∧
      Function.Semiconj (δ r) (C r).frobenius (A (r + 1)).frobenius)
    (m : ℕ) (s : Finset ℤ)
    (hA : ∀ r ∉ s, Subsingleton (A r).carrier) (hB : ∀ r ∉ s, Subsingleton (B r).carrier)
    (hC : ∀ r ∉ s, Subsingleton (C r).carrier) :
    (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace K _ ((B r).frobeniusEnd ^ m)) =
      (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace K _ ((A r).frobeniusEnd ^ m)) +
        ∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace K _ ((C r).frobeniusEnd ^ m) := by
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun r ↦ (A r).carrier) (fun r ↦ (B r).carrier) (fun r ↦ (C r).carrier)
    f g (fun r _ he ↦ he ▸ δ r) (fun r ↦ (h r).1)
    (fun r r' he ↦ by subst r'; exact (h r).2.1)
    (fun r r' he ↦ by subst r'; exact (h r).2.2.1) _ _ _
    (fun r ↦ FrobeniusModule.frobeniusEnd_pow_comp _ (h r).2.2.2.1 m)
    (fun r ↦ FrobeniusModule.frobeniusEnd_pow_comp _ (h r).2.2.2.2.1 m)
    (fun r r' he ↦ by subst r'; exact FrobeniusModule.frobeniusEnd_pow_comp _ (h r).2.2.2.2.2 m)
    s hA hB hC

end WeilII
