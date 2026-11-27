module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.StalkTensorTrace
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.FrobeniusTwist
public import WeilConjectures.WeilSheaf.TraceFunctionOps
import WeilConjectures.ZetaFunction.TraceFormula

/-! # The twisted closed term of the divisor trace formula

Zhang, equation (2.2.1), p. 3, and SGA 4½, Rapport sur la formule des traces, Théorème 3.2. -/

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace WeilII

universe u

/-- The alternating power trace of the pulled-back sheaf with twist minus one and
cohomological shift by two equals the sum of the original point traces on the source
times the size of the extension field. The shift preserves the parity of every degree.
Apply the trace formula on the source. The Tate sheaf is a constant twist of the unit
whose m-th Frobenius has scalar (#k)^m. Pullback evaluates at the image of the point
and tensoring multiplies the two traces. Source: Zhang, equation (2.2.1), p. 3. -/
public theorem shiftedTate_alternatingTrace_eq_card_mul_sum
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (i : Y ⟶ X) [i.IsOver (Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (G : WeilSheaf k ℓ X) (hG : G.IsLisse) {m : ℕ} (hm : 1 ≤ m) :
    let L := FiniteField.galoisExtension k m
    let T := ((WeilSheaf.upperStar i).obj G).tensorObj (WeilSheaf.tateTwistSheaf k ℓ Y (-1))
      (hG.upperStar i)
    (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl ℓ) _
      ((T.compactlySupportedCohomology (r - 2)).frobeniusEnd ^ m)) =
        (Nat.card k : PadicAlgCl ℓ) ^ m *
          ∑ᶠ y : (Y ↘ Spec (CommRingCat.of k)).fieldPoints L,
            G.traceFunction m (i.mapFieldPoints L y) := by
  intro L T
  have ht (y : (Y ↘ Spec (CommRingCat.of k)).fieldPoints L) :
      T.traceFunction m y = (Nat.card k : PadicAlgCl ℓ) ^ m *
        G.traceFunction m (i.mapFieldPoints L y) := by
    let twist := WeilSheaf.tateTwistSheaf k ℓ Y (-1)
    obtain ⟨c, hc, ⟨e⟩⟩ := WeilSheaf.exists_tateTwistSheaf_neg_iso_constantTwist k ℓ Y 1
    have he := WeilSheaf.traceFunction_congr e m y
    rw [WeilSheaf.traceFunction_constantTwist, WeilSheaf.traceFunction_adicConstant,
      mul_one, hc, pow_one] at he
    exact (WeilSheaf.traceFunction_tensorObj _ twist (hG.upperStar i) m y).trans
      (congrArg₂ (· * ·) he (WeilSheaf.traceFunction_upperStar i G m y))
  have ha : (∑ᶠ r : ℤ, (r.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl ℓ) _
      ((T.compactlySupportedCohomology (r - 2)).frobeniusEnd ^ m)) =
      ∑ᶠ y : (Y ↘ Spec (CommRingCat.of k)).fieldPoints L, T.traceFunction m y := by
    let tr := fun r : ℤ ↦ LinearMap.trace (PadicAlgCl ℓ) _
      ((T.compactlySupportedCohomology r).frobeniusEnd ^ m)
    calc
      _ = ∑ᶠ r : ℤ, ((r - 2).negOnePow : ℤ) • tr (r - 2) := by
        apply finsum_congr
        intro r
        simp only [Int.negOnePow_sub, show (2 : ℤ).negOnePow = 1 by decide, mul_one]
        rfl
      _ = ∑ᶠ r : ℤ, (r.negOnePow : ℤ) • tr r :=
        finsum_comp_equiv (Equiv.subRight (2 : ℤ)) (f := fun r ↦ (r.negOnePow : ℤ) • tr r)
      _ = _ := ((WeilSheaf.toComplex.obj T).finsum_trace_compactlySupportedCohomology_eq hm).trans
        (finsum_congr (WeilComplex.traceFunction_toComplex T m))
  exact ha.trans ((finsum_congr ht).trans (mul_finsum _ _).symm)

end WeilII
