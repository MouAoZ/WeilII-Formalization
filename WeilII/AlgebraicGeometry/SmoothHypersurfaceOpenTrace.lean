module

public import WeilII.AlgebraicGeometry.SmoothHypersurfaceGysinSequence
public import WeilConjectures.WeilSheaf.TraceFunctionOps
import WeilConjectures.ZetaFunction.TraceFormula
import WeilII.AlgebraicGeometry.ShiftedTateTrace
import WeilII.LinearAlgebra.AlternatingFrobeniusTrace

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Zhang, equation (2.2.1). For any lisse Weil sheaf, the alternating trace on the
open direct image is the ambient point sum minus the contribution of the smooth divisor.
Bound all three terms of the Gysin sequence in a common interval, shifting the bounds
on the divisor by two. Trace additivity gives the difference. The trace formula on the
ambient space and the shifted Tate trace formula on the divisor evaluate its two terms. -/
public theorem smoothHypersurface_openTrace_eq_sub
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {n : ℕ} {Y : Scheme.{u}}
    (i : Y ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) [IsSmoothAffineHypersurface i]
    (G : WeilSheaf k ℓ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))) (hG : G.IsLisse)
    {m : ℕ} (hm : 1 ≤ m) :
    let a := 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)
    letI : Y.Over (Spec (CommRingCat.of k)) := ⟨i ≫ a⟩
    letI : i.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
    letI := isNoetherian_of_locallyOfFiniteType a
    let D := openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G
    let L := FiniteField.galoisExtension k m
    (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl ℓ) _
      ((D.compactlySupportedCohomology r).frobeniusEnd ^ m)) =
      (∑ᶠ x : a.fieldPoints L, G.traceFunction m x) - (Nat.card k : PadicAlgCl ℓ) ^ m *
        ∑ᶠ y : (i ≫ a).fieldPoints L, G.traceFunction m (i.mapFieldPoints L y) := by
  intro projection openImage L
  -- Keep the three cohomology families as local definitions while evaluating their traces.
  refine (fun (deduce : _ → _) ↦ deduce (smoothHypersurfaceGysinSequence i G hG)) ?_
  lift_lets -merge -underBinder
  intro a T j D η A B C res sequence
  letI : Y.Over (Spec (CommRingCat.of k)) := ⟨i ≫ a⟩
  letI : i.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  letI : IsSeparated (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsSeparated (i ≫ a))
  letI : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ a))
  letI : QuasiCompact (Y ↘ Spec (CommRingCat.of k)) := inferInstanceAs (QuasiCompact (i ≫ a))
  let alt (V : ℤ → FrobeniusModule.{u + 1} (PadicAlgCl ℓ)) :=
    ∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl ℓ) _ ((V r).frobeniusEnd ^ m)
  have addTrace : alt B = alt A + alt C := by
    obtain ⟨f, δ, hex⟩ := sequence
    obtain ⟨aT, bT, hT⟩ :=
      (WeilSheaf.toComplex.obj T).exists_subsingleton_compactlySupportedCohomology
    obtain ⟨aG, bG, hB⟩ :=
      (WeilSheaf.toComplex.obj G).exists_subsingleton_compactlySupportedCohomology
    obtain ⟨aD, bD, hC⟩ := D.exists_subsingleton_compactlySupportedCohomology
    let s := Finset.Icc (min (aT + 2) (min aG aD)) (max (bT + 2) (max bG bD))
    exact alternatingTrace_eq_add_of_frobeniusExact A B C f res δ hex m s
      (fun r hr ↦ hT (r - 2) (by simp only [s, Finset.mem_Icc] at hr; omega))
      (fun r hr ↦ hB r (by simp only [s, Finset.mem_Icc] at hr; omega))
      (fun r hr ↦ hC r (by simp only [s, Finset.mem_Icc] at hr; omega))
  let tx (x : a.fieldPoints L) := G.traceFunction m x
  let ty (y : (i ≫ a).fieldPoints L) := G.traceFunction m (i.mapFieldPoints L y)
  have affineTrace : alt B = finsum tx :=
    ((WeilSheaf.toComplex.obj G).finsum_trace_compactlySupportedCohomology_eq hm).trans
      (finsum_congr (WeilComplex.traceFunction_toComplex G m))
  have closedTrace : alt A = (Nat.card k : PadicAlgCl ℓ) ^ m * finsum ty :=
    shiftedTate_alternatingTrace_eq_card_mul_sum i G hG hm
  exact (eq_sub_of_add_eq' addTrace.symm).trans (congrArg₂ (· - ·) affineTrace closedTrace)

end WeilII
