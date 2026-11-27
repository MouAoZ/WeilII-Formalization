module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilII.Paper.SmoothAffineHypersurface
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.RingTheory.BertiniHypersurface

/-!
# Jacobian criterion for an affine hypersurface

Zhang, *On an elementary proof of Weil II*, Construction 2.5, p. 3, uses smoothness
of a hypersurface defined by a polynomial in affine coordinates.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The hypersurface criterion used in Zhang, Construction 2.5, p. 3. If a nonzero
nonunit polynomial and its partial derivatives generate the unit ideal, its zero
locus is a smooth hypersurface over the coefficient field.

Write `S = k[X₁,…,Xₙ]`. The ideal hypothesis gives a relation
`1 = a f + ∑ bᵢ ∂ᵢf`. The derivation `D = ∑ bᵢ ∂ᵢ` then has `D(f) − 1 ∈ (f)`.
Since the polynomial algebra is formally smooth,
`Algebra.FormallySmooth.quotient_span_singleton_of_derivation` gives formal
smoothness of `S/(f)`. The quotient has a presentation with `n` generators and
one relation, hence is smooth over `k`.

Evaluation at the affine coordinates identifies `S` with the global sections
of affine space, taking `f` to the section `s` below. On this affine chart the
ideal sheaf of the zero locus has ideal `(s)`, and the inclusion induces the
quotient map on global sections. Thus the zero locus is affine with coordinate
ring `S/(f)`, and its structure morphism to `Spec k` is smooth. Multiplication
by `f` is injective in the polynomial domain, so the singleton `[s]` is a weakly
regular sequence generating the kernel ideal on the whole chart. This witnesses
a regular closed immersion of codimension one. -/
public theorem isSmoothAffineHypersurface_of_unitJacobianIdeal
    {k : Type u} [Field k] {n : ℕ} (hn : 2 ≤ n) (f : MvPolynomial (Fin n) k)
    (hf : f ≠ 0) (hfu : ¬ IsUnit f)
    (hJ : Ideal.span (insert f (Set.range fun i : Fin n ↦ MvPolynomial.pderiv i f)) = ⊤) :
    let S := Spec (CommRingCat.of k)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ S).appTop).hom
    let s := MvPolynomial.eval₂Hom coeff (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i)) f
    IsSmoothAffineHypersurface (X.zeroLocusSubschemeι {s}) := by
  classical
  -- The calculation also applies to an empty zero locus and to any finite number of variables.
  clear hn hfu
  let A := MvPolynomial (Fin n) k
  let J : Ideal A := Ideal.span {f}
  let B := A ⧸ J
  obtain ⟨u, z, hz, hbez⟩ := Ideal.mem_span_insert.mp ((Ideal.eq_top_iff_one _).mp hJ)
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hz
  let D : Derivation k A A := ∑ i, b i • MvPolynomial.pderiv i
  have hD : D f = z := by
    change (∑ i, b i • MvPolynomial.pderiv i : Derivation k A A).toLinearMap f = z
    simpa [Derivation.coe_sum_linearMap] using hb
  have hform : Algebra.FormallySmooth k B := by
    apply Algebra.FormallySmooth.quotient_span_singleton_of_derivation D
    refine Ideal.mem_span_singleton.mpr ⟨-u, ?_⟩
    rw [hD]
    linear_combination -hbez
  have hfp : Algebra.FinitePresentation k B :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton f)
  have hsm : (algebraMap k B).Smooth := RingHom.smooth_algebraMap.mpr ⟨hform, hfp⟩
  let R := CommRingCat.of k
  let S := Spec R
  let X := 𝔸(ULift.{u} (Fin n); S)
  let π := X ↘ S
  let coeff := ((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom
  let ev : A →+* Γ(X, ⊤) :=
    MvPolynomial.eval₂Hom coeff (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i))
  have hev : Function.Bijective ev := by
    let e := MvPolynomial.renameEquiv k (Equiv.ulift.{u} (α := Fin n)).symm
    let ev' := MvPolynomial.eval₂Hom coeff (AffineSpace.coord (n := ULift.{u} (Fin n)) S)
    have he (g : A) : ev' (e g) = ev g := MvPolynomial.eval₂Hom_rename _ _ _ _
    have heq : ev' ∘ e = ev := funext he
    rw [← heq]
    exact (AffineSpace.bijective_eval₂Hom_coord R).comp e.bijective
  let s := ev f
  let I : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {s})
  let i := I.subschemeι
  change IsSmoothAffineHypersurface i
  have hX : IsAffine X := isAffine_of_isAffineHom π
  have htop : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {s} :=
    Scheme.IdealSheafData.ideal_top_ofIdealTop _
  have hreg : IsRegularImmersion 1 i := by
    constructor
    intro x
    refine ⟨⟨⊤, isAffineOpen_top X⟩, trivial, [s], rfl, ?_, ?_⟩
    · apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
      have : IsDomain Γ(X, ⊤) := (RingEquiv.ofBijective ev hev).symm.toMulEquiv.isDomain
      have hs : s ≠ 0 := fun h ↦ hf (hev.injective (by simpa using h))
      exact fun a b h ↦ mul_left_cancel₀ hs h
    · rw [Ideal.ofList_singleton, show i.ker = I from I.ker_subschemeι, htop]
  have hi := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have hY : IsAffine I.subscheme := hi.1
  let g := i.appTop.hom.comp ev
  have hsurj : Function.Surjective g := hi.2.comp hev.2
  have hker : RingHom.ker g = J := by
    have hki : RingHom.ker i.appTop.hom = Ideal.span {s} :=
      (I.ker_subschemeι_app ⟨⊤, isAffineOpen_top X⟩).trans htop
    have him : J.map ev = Ideal.span {s} := by simp [J, s, Ideal.map_span]
    change RingHom.ker (i.appTop.hom.comp ev) = J
    rw [← RingHom.comap_ker, hki, ← him]
    exact Ideal.comap_map_of_bijective ev hev
  let eY : B ≃+* Γ(I.subscheme, ⊤) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hm (p : A) : eY (Ideal.Quotient.mk J p) = g p := by
    exact (congrArg (g.quotientKerEquivOfSurjective hsurj)
      (Ideal.quotEquivOfEq_mk hker.symm p)).trans
        (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj p)
  refine { hreg with toSmooth := ?_ }
  apply (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := i ≫ π)).mpr
  apply (RingHom.Smooth.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso R).inv
    (i ≫ π).appTop).mp
  have hbase : (i ≫ π).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom =
      eY.toRingHom.comp (algebraMap k B) := by
    ext r
    change _ = eY (Ideal.Quotient.mk J (MvPolynomial.C r))
    rw [hm, Scheme.Hom.comp_appTop]
    exact (congrArg i.appTop (MvPolynomial.eval₂Hom_C coeff _ r)).symm
  rw [hbase]
  exact RingHom.Smooth.respectsIso.1 _ eY hsm

end WeilII
