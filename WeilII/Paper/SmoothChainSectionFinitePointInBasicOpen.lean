module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilII.Paper.ChainSectionPolynomial
public import WeilII.Paper.SmoothAffineHypersurface
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.RingHom.Smooth
import WeilII.Paper.ChainSectionGenericSmoothness
import WeilII.AlgebraicGeometry.SmoothAffineHypersurfaceDescent

/-!
# A finite-extension smooth chain section in a prescribed principal open

This is the finite-extension choice of parameters in Dingxin Zhang,
*On an elementary proof of Weil II*, Construction 2.5, pp. 2–3.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- In the normalized parameter chart of Zhang's Construction 2.5, every nonempty principal
open over the algebraic closure contains a tuple defined over a finite intermediate field
whose chain section is smooth over that field.

Proof. Let `K` be the algebraic closure of `k`. Choose the nonzero polynomial `h` from
`exists_smooth_chainSection_basicOpen`. The product `g * h` is nonzero in the polynomial
ring over the field `K`. Since `K` is infinite, polynomial function extensionality gives
a tuple where the product is nonzero. At this tuple both factors are nonzero, so the
section is smooth over `K`. Adjoin the entries of the tuple to `k` inside `K`. These
finitely many integral elements generate a finite extension `L`. Their images in `K`
recover the tuple, so evaluation of `g` there is still nonzero.

Write `P` for the chain polynomial over `L`. Its zero locus in affine space has coordinate
ring `L[X]/(P)`, since evaluation at the affine coordinates identifies the defining section
with `P`. Tensoring this presentation with `K` gives the coordinate ring of the smooth
section just selected. Smoothness of the quotient algebra descends along the faithfully
flat field extension `K/L`, so the zero locus is smooth over `L`. Since `n ≥ 2`, the
coefficient of `X₁X₂` in `P` is one. Thus `P` is a nonzero nonunit in the polynomial
domain. It generates the kernel of the quotient map as a regular sequence of length one,
giving the required regular closed immersion. -/
public theorem exists_smooth_chainSection_finitePoint_in_basicOpen (k : Type u) [Field k] [Finite k]
    (n : ℕ) (hn : 2 ≤ n) (g : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)) (hg : g ≠ 0) :
    ∃ L : IntermediateField k (AlgebraicClosure k), FiniteDimensional k L ∧
      ∃ (a : Fin n → L) (c : L),
        MvPolynomial.eval (Fin.snoc (fun i ↦ (a i : AlgebraicClosure k)) (c : AlgebraicClosure k))
          g ≠ 0 ∧
        let S := Spec (CommRingCat.of L)
        let X := 𝔸(ULift.{u} (Fin n); S)
        let coeff := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (X ↘ S).appTop).hom
        let p := MvPolynomial.eval₂Hom coeff (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i))
          (chainSectionPolynomial a c)
        IsSmoothAffineHypersurface (X.zeroLocusSubschemeι {p}) := by
  classical
  let K := AlgebraicClosure k
  obtain ⟨h, hh, _, smooth⟩ := exists_smooth_chainSection_basicOpen K n hn
  -- Avoid the hyperplane c = 0 as well, so the section is nonzero at the origin.
  let F := g * h * MvPolynomial.X (Fin.last n)
  have hF : F ≠ 0 := mul_ne_zero (mul_ne_zero hg hh) (MvPolynomial.X_ne_zero _)
  obtain ⟨x, hx⟩ : ∃ x : Fin (n + 1) → K, MvPolynomial.eval x F ≠ 0 := by
    by_contra! hz
    exact hF (MvPolynomial.funext fun x ↦ by simpa using hz x)
  simp only [F, map_mul, MvPolynomial.eval_X] at hx
  let L := IntermediateField.adjoin k (Set.range x)
  let y (i : Fin (n + 1)) : L := ⟨x i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
  let a := Fin.init y
  let c := y (Fin.last n)
  have hx' : Fin.snoc (fun i ↦ (a i : K)) (c : K) = x := Fin.snoc_init_self x
  refine ⟨L, inferInstance, a, c, ?_, ?_⟩
  · rw [hx']
    exact left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hgeom := smooth (fun i ↦ (a i : K)) (c : K) (by
    rw [hx']
    exact right_ne_zero_of_mul (left_ne_zero_of_mul hx))
  intro S X coeff p
  let T := Spec (CommRingCat.of K)
  let Y := 𝔸(ULift.{u} (Fin n); T)
  let coeffK := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Y ↘ T).appTop).hom
  let φ := CommRingCat.ofHom (algebraMap L K)
  let b := AffineSpace.map (ULift.{u} (Fin n)) (Spec.map φ)
  let P := chainSectionPolynomial a c
  have hp : p ≠ 0 := by
    let o := AffineSpace.homOfVector (𝟙 S) (0 : ULift.{u} (Fin n) → Γ(S, ⊤))
    have hc₀ : c ≠ 0 := fun e ↦ right_ne_zero_of_mul hx (show (c : K) = 0 by simp [e])
    have hconst : MvPolynomial.constantCoeff P = c := by
      cases n <;> simp [P, chainSectionPolynomial, map_sum]
    intro e
    have hz := congrArg o.appTop.hom e
    change o.appTop.hom (MvPolynomial.eval₂Hom coeff _ P) = o.appTop.hom 0 at hz
    rw [MvPolynomial.map_eval₂Hom, map_zero] at hz
    have ho (i : Fin n) : o.appTop.hom (AffineSpace.coord S (ULift.up.{u} i)) = 0 :=
      AffineSpace.homOfVector_appTop_coord _ _ _
    simp only [ho, MvPolynomial.eval₂Hom_zero', RingHom.comp_apply, hconst] at hz
    exact hc₀ ((o.appTop.hom.comp coeff).injective (by simpa using hz))
  apply isSmoothAffineHypersurface_of_smooth_fieldExtension (K := K) p hp
  have hcoeff : b.appTop.hom.comp coeff = coeffK.comp (algebraMap L K) := by
    change ((Scheme.ΓSpecIso (.of L)).inv ≫ (X ↘ S).appTop ≫ b.appTop).hom =
      (φ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ T).appTop).hom
    rw [← Scheme.Hom.comp_appTop, AffineSpace.map_over, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  have hmap : MvPolynomial.map (algebraMap L K) P =
      chainSectionPolynomial (fun i ↦ (a i : K)) (c : K) := by
    cases n <;> simp [P, chainSectionPolynomial, map_sum]
  have hsection : b.appTop p = MvPolynomial.eval₂Hom coeffK
      (fun i : Fin n ↦ AffineSpace.coord T (ULift.up.{u} i))
      (chainSectionPolynomial (fun i ↦ (a i : K)) (c : K)) := by
    change b.appTop.hom (MvPolynomial.eval₂Hom coeff _ P) = _
    rw [MvPolynomial.map_eval₂Hom, hcoeff, ← hmap, MvPolynomial.eval₂Hom_map_hom]
    have hb (i : Fin n) : b.appTop.hom (AffineSpace.coord S (ULift.up.{u} i)) =
        AffineSpace.coord T (ULift.up.{u} i) := AffineSpace.map_appTop_coord _ _
    simp only [hb]
  change Smooth (Y.zeroLocusSubschemeι {b.appTop p} ≫ (Y ↘ T))
  rw [hsection]
  exact hgeom.toSmooth

end WeilII
