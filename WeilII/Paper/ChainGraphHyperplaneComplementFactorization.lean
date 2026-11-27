module

public import Mathlib.Algebra.MvPolynomial.Eval
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilII.Paper.ChainSectionPolynomial
import WeilII.Paper.NormalizedProjectiveHyperplaneChart
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The chain graph on the complement of a normalized hyperplane

Zhang, *On an elementary proof of Weil II*, Construction 2.5, p. 3, gives the chain graph
and the hyperplane equation. The open and closed immersions below give the compactification
used in Katz, *Affine cohomological transforms, perversity, and monodromy*, A.6, p. 221.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace Scheme.Modules

universe u

/-- In Zhang's Construction 2.5, let `λ = zₙ₊₁ + a·z + c z₀`. On the complement of
this hyperplane the chain graph factors through the hypersurface
`Z = V(t(1 − a·v − ct) − Q(v))` in affine space with coordinates `(t,v) = (z₀/λ,z/λ)`.
The restricted graph identifies its source with the principal open `D_Z(t)`.

Proof. Replacing the last homogeneous coordinate by λ is an invertible linear change
over K, with inverse given by subtracting a·z + c z₀. Its last standard chart identifies
the hyperplane complement B with affine (n+1)-space over K. In this chart the missing
coordinate zₙ₊₁/λ is 1 − a·v − ct. On the graph [1 : x : Q(x)] the equation λ restricts
to P = Q(x) + a·x + c. Thus the inverse image of B is D(P), and the restricted graph has
affine coordinates t = 1/P and v = x/P.

Substituting these coordinates into the equation of Z gives zero since Q is homogeneous
of degree two. The quotient of K[t,v] by this equation defines the closed immersion
Z ↪ B. On D_Z(t) put x = v/t. Dividing the equation by t² gives P(v/t) = 1/t. The
two substitutions therefore induce maps on the localized coordinate rings, inverse on
each generator and its inverted denominator. Their spectra give D(P) ≅ D_Z(t), with
the asserted composite into B. This works in every characteristic.

The quotient defining Z is a finitely generated K-algebra, so Z is affine of finite type.
The coefficient of the degree-one monomial t is one. Thus each prime in a chain defining
the dimension of Z lifts to a nonzero prime of K[t,v]. Prepending the zero prime gives a
strictly longer chain in a polynomial ring of dimension n+1, proving dim Z ≤ n. -/
public theorem chainGraph_hyperplaneComplement_factorization
    (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n) (a : Fin n → K) (c : K) :
    let S := Spec (CommRingCat.of K)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let A := 𝔸(ULift.{u} (Fin (n + 1)); S)
    let J := ULift.{u} (Fin (n + 2))
    let coeff := fun {Y : Scheme.{u}} (s : Y ⟶ S) ↦ ((Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop).hom
    let x := fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i)
    let Q := chainSectionPolynomial (0 : Fin n → K) 0
    let evX := MvPolynomial.eval₂Hom (coeff (X ↘ S)) x
    let p := evX (chainSectionPolynomial a c)
    let V := X.basicOpen p
    let graphTuple : Fin (n + 2) → Γ(X, ⊤) := Fin.cons 1 (Fin.snoc x (evX Q))
    let graphCoords := fun j : J ↦ graphTuple j.down
    let f := homOfSections (X ↘ S) graphCoords
      ((Ideal.eq_top_iff_one _).mpr (Ideal.subset_span (s := Set.range graphCoords)
        ⟨⟨0⟩, by simp [graphCoords, graphTuple]⟩))
    let z := twistOneSection J S
    let lam := z ⟨Fin.last (n + 1)⟩ +
      (∑ i : Fin n, coeff (ℙ(J; S) ↘ S) (a i) • z ⟨i.succ.castSucc⟩) +
      coeff (ℙ(J; S) ↘ S) c • z ⟨0⟩
    let B := (homOfGlobalSection _ lam).zeroLocus.subschemeι.openComplement
    let lamB : Γ(twistRestrict B.ι 1, ⊤) := pullbackSection B.ι lam
    let coord := fun j : Fin (n + 1) ↦ AffineSpace.coord S (ULift.up.{u} j)
    let t := coord 0
    let v := fun i : Fin n ↦ coord i.succ
    let last := 1 - (∑ i, coeff (A ↘ S) (a i) * v i) - coeff (A ↘ S) c * t
    let F := t * last - MvPolynomial.eval₂Hom (coeff (A ↘ S)) v Q
    let Z := A.zeroLocusSubscheme {F}
    let b := A.zeroLocusSubschemeι {F}
    let U := Z.basicOpen (b.appTop t)
    let numer : Fin (n + 1) → Γ(X, ⊤) := Fin.cons 1 x
    let g := AffineSpace.homOfVector (V.ι ≫ X ↘ S)
      (fun j : ULift.{u} (Fin (n + 1)) ↦ X.divBasicOpen (numer j.down) p)
    f ⁻¹ᵁ B = V ∧ IsAffine Z ∧ LocallyOfFiniteType (b ≫ A ↘ S) ∧ QuasiCompact (b ≫ A ↘ S) ∧
      topologicalKrullDim Z ≤ (n : WithBot ℕ∞) ∧
      ∃ (chart : B.toScheme ≅ A) (e : V.toScheme ≅ U.toScheme),
        chart.hom ≫ A ↘ S = B.ι ≫ ℙ(J; S) ↘ S ∧
        (∀ j : Fin (n + 1), chart.hom.appTop (coord j) • lamB =
          pullbackSection B.ι (z ⟨j.castSucc⟩)) ∧
        g ≫ chart.inv ≫ B.ι = V.ι ≫ f ∧ e.hom ≫ U.ι ≫ b = g := by
  classical
  intro S X A J coeff x Q evX p V graphTuple graphCoords f z lam B lamB
    coord t v last F Z b U numer g
  have hA : IsAffine A := isAffine_of_isAffineHom (A ↘ S)
  have hX : IsAffine X := isAffine_of_isAffineHom (X ↘ S)
  have hZ : IsAffine Z := isAffine_of_isAffineHom b
  have hF : F ≠ 0 := by
    -- At t = 0 and v = (1, 1, 0, …), the chain quadratic is one.
    let w : ULift.{u} (Fin (n + 1)) → Γ(S, ⊤) :=
      fun j ↦ if j.down.val = 1 ∨ j.down.val = 2 then 1 else 0
    let test := AffineSpace.homOfVector (𝟙 S) w
    have hw (j : Fin (n + 1)) : test.appTop (coord j) = w ⟨j⟩ :=
      AffineSpace.homOfVector_appTop_coord ..
    have ht : test.appTop t = 0 := by simp [t, hw, w]
    have hq : test.appTop (MvPolynomial.eval₂Hom (coeff (A ↘ S)) v Q) = 1 := by
      cases n with
      | zero => omega
      | succ k =>
        cases k with
        | zero => omega
        | succ k =>
          simp only [Q, chainSectionPolynomial, Pi.zero_apply, map_zero, zero_mul,
            Finset.sum_const_zero, add_zero, map_sum, map_mul, MvPolynomial.eval₂Hom_X', v, hw]
          rw [Finset.sum_eq_single (0 : Fin (k + 1))]
          · simp [w]
          · intro i _ hi
            simp [w, hi]
          · simp
    intro h
    have h' := congrArg (fun s : Γ(A, ⊤) ↦ test.appTop s) h
    simp only [F, map_sub, map_mul, ht, zero_mul, hq, zero_sub, map_zero, neg_eq_zero] at h'
    exact one_ne_zero h'
  have hdA : topologicalKrullDim A ≤ (n : WithBot ℕ∞) + 1 := by
    simpa only [Nat.cast_succ] using
      topologicalKrullDim_le_of_smoothOfRelativeDimension (A ↘ S) (n + 1)
  have hdZ : topologicalKrullDim Z ≤ (n : WithBot ℕ∞) := by
    apply ENat.WithBot.lt_add_one_iff.mp
    apply lt_of_lt_of_le _ hdA
    have emb := b.isClosedEmbedding
    apply lt_of_le_of_ne emb.isInducing.topologicalKrullDim_le
    intro he
    have finiteDim : (n : WithBot ℕ∞) + 1 ≠ ⊤ := by
      rw [← Nat.cast_succ]
      exact mt WithBot.coe_eq_top.mp (ENat.natCast_ne_top _)
    have sur := emb.isInducing.surjective_of_topologicalKrullDim_eq emb.isClosed_range
      (ne_top_of_le_ne_top finiteDim hdA) he
    apply hF
    apply (basicOpen_eq_bot_iff F).mp
    apply eq_bot_iff.mpr
    intro y hy
    obtain ⟨z, hz⟩ := sur y
    have hz' : y ∈ Set.range (A.zeroLocusSubschemeι {F}).base := ⟨z, hz⟩
    rw [A.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι] at hz'
    exact hz' hy
  have coeff_comp {Y T : Scheme.{u}} (h : Y ⟶ T) (s : T ⟶ S) (k : K) :
      h.appTop (coeff s k) = coeff (h ≫ s) k := by
    dsimp only [coeff]
    rw [Scheme.Hom.comp_appTop]
    rfl
  -- Substituting v = t x gives F = t − t² P(x) on every test scheme.
  have equation {Y : Scheme.{u}} (r : Y ⟶ X) (d : Y ⟶ A)
      (hbase : d ≫ A ↘ S = r ≫ X ↘ S)
      (hv : ∀ i, d.appTop (v i) = d.appTop t * r.appTop (x i)) :
      d.appTop F = d.appTop t - d.appTop t ^ 2 * r.appTop p := by
    have hc (k : K) : d.appTop (coeff (A ↘ S) k) = r.appTop (coeff (X ↘ S) k) := by
      rw [coeff_comp, coeff_comp, hbase]
    cases n with
    | zero => omega
    | succ m =>
      simp only [F, last, Q, p, evX, chainSectionPolynomial, Pi.zero_apply, map_zero,
        zero_mul, Finset.sum_const_zero, add_zero, map_add, map_sub, map_mul, map_one,
        map_sum, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, hv, hc,
        mul_add, Finset.mul_sum]
      ring_nf
      simp only [Finset.mul_sum]
      ring_nf
  have hg_base : g ≫ A ↘ S = V.ι ≫ X ↘ S := AffineSpace.homOfVector_over ..
  have hg_coord (j : Fin (n + 1)) : g.appTop (coord j) = X.divBasicOpen (numer j) p :=
    AffineSpace.homOfVector_appTop_coord ..
  have htp : g.appTop t * V.ι.appTop p = 1 := by
    rw [show t = coord 0 from rfl, hg_coord]
    simpa [numer] using X.divBasicOpen_mul_self (numer 0) p
  have hgt : IsUnit (g.appTop t) := IsUnit.of_mul_eq_one _ htp
  have hgv (i : Fin n) : g.appTop (v i) = g.appTop t * V.ι.appTop (x i) := by
    apply (X.isUnit_ι_appTop_basicOpen p).mul_right_cancel
    rw [mul_right_comm (g.appTop t), htp, one_mul, show v i = coord i.succ from rfl, hg_coord]
    simpa [numer] using X.divBasicOpen_mul_self (numer i.succ) p
  have hgF : g.appTop F = 0 := by
    rw [equation V.ι g hg_base hgv, pow_two, mul_assoc, htp, mul_one, sub_self]
  have hV : IsAffine V.toScheme := (isAffineOpen_top X).basicOpen p
  have : QuasiCompact g := inferInstance
  let gZ := g.liftZeroLocusSubscheme (s := {F}) (by simpa using hgF)
  have hgZ : gZ ≫ b = g := Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι ..
  have liftOpen {Y T : Scheme.{u}} (h : Y ⟶ T) (s : Γ(T, ⊤)) (hu : IsUnit (h.appTop s)) :
      ∃ l : Y ⟶ (T.basicOpen s).toScheme, l ≫ (T.basicOpen s).ι = h := by
    have hpre : h ⁻¹ᵁ T.basicOpen s = ⊤ := by
      rw [Scheme.preimage_basicOpen_top, Y.basicOpen_of_isUnit hu]
    have hrange : Set.range h ⊆ Set.range (T.basicOpen s).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hpre.ge (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  obtain ⟨forward, hforward⟩ := liftOpen gZ (b.appTop t) (by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hgZ]
    exact hgt)
  have forward_fac : forward ≫ U.ι ≫ b = g := by rw [← Category.assoc, hforward, hgZ]
  -- On D_Z(t), the inverse morphism has coordinates xᵢ = vᵢ/t.
  let d := U.ι ≫ b
  let r := AffineSpace.homOfVector (d ≫ A ↘ S)
    (fun j : ULift.{u} (Fin n) ↦ Z.divBasicOpen (b.appTop (v j.down)) (b.appTop t))
  have rbase : r ≫ X ↘ S = d ≫ A ↘ S := AffineSpace.homOfVector_over ..
  have ru : IsUnit (d.appTop t) := Z.isUnit_ι_appTop_basicOpen _
  have rv (i : Fin n) : d.appTop (v i) = d.appTop t * r.appTop (x i) := by
    rw [show r.appTop (x i) = _ from AffineSpace.homOfVector_appTop_coord .., mul_comm]
    exact (Z.divBasicOpen_mul_self _ _).symm
  have hdt : d.appTop t * r.appTop p = 1 := by
    apply ru.mul_left_cancel
    have hf : d.appTop F = 0 := by
      simp only [d, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, b,
        A.zeroLocusSubschemeι_appTop (Set.mem_singleton F), map_zero]
    rw [equation r d rbase.symm rv, sub_eq_zero] at hf
    rw [mul_one, ← mul_assoc, ← pow_two, ← hf]
  obtain ⟨backward, hbackward⟩ := liftOpen r p (IsUnit.of_mul_eq_one_right _ hdt)
  -- Verify the composites after the monomorphisms into the affine spaces.
  have pull {Y T W : Scheme.{u}} {h : Y ⟶ T} {i : T ⟶ W} {j : Y ⟶ W}
      (fac : h ≫ i = j) (s : Γ(W, ⊤)) : h.appTop (i.appTop s) = j.appTop s := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, fac]
  have forward_r : forward ≫ r = V.ι := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, rbase, ← Category.assoc, show forward ≫ d = g from forward_fac, hg_base]
    · rintro ⟨i⟩
      change (forward ≫ r).appTop (x i) = V.ι.appTop (x i)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      apply hgt.mul_left_cancel
      have h := congrArg (fun s : Γ(U, ⊤) ↦ forward.appTop s) (rv i)
      simp only [map_mul, pull (i := d) forward_fac] at h
      exact h.symm.trans (hgv i)
  have backward_g : backward ≫ g = d := by
    have bt : backward.appTop (g.appTop t) = d.appTop t := by
      apply (IsUnit.of_mul_eq_one_right _ hdt).mul_right_cancel
      have h := congrArg (fun s : Γ(V, ⊤) ↦ backward.appTop s) htp
      simp only [map_mul, map_one] at h
      rw [pull hbackward p] at h
      exact h.trans hdt.symm
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hg_base, ← Category.assoc, hbackward, rbase]
    · rintro ⟨j⟩
      induction j using Fin.cases with
      | zero => exact bt
      | succ i =>
        change backward.appTop (g.appTop (v i)) = d.appTop (v i)
        rw [hgv, map_mul, bt, pull hbackward, rv]
  let e : V.toScheme ≅ U.toScheme :=
    { hom := forward
      inv := backward
      hom_inv_id := by
        apply (cancel_mono V.ι).mp
        rw [Category.assoc, hbackward, forward_r, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono (U.ι ≫ b)).mp
        rw [Category.assoc, forward_fac, backward_g, Category.id_comp] }
  let l : Fin (n + 1) → Γ(S, ⊤) := Fin.cons ((Scheme.ΓSpecIso (.of K)).inv c)
    (fun i ↦ (Scheme.ΓSpecIso (.of K)).inv (a i))
  have hLam : lam = z ⟨Fin.last (n + 1)⟩ +
      ∑ j : Fin (n + 1), (ℙ(J; S) ↘ S).appTop (l j) • z ⟨j.castSucc⟩ := by
    rw [Fin.sum_univ_succ]
    change _ + _ + _ = _ + (_ + _)
    simp only [l, Fin.cons_succ, Fin.cons_zero, coeff, CommRingCat.hom_comp, RingHom.comp_apply]
    abel
  obtain ⟨chart, chartbase, chartcoord, chartpull⟩ := normalizedHyperplaneChart S (n + 1) l lam hLam
  have hfirst : graphCoords ⟨0⟩ = 1 := by simp [graphCoords, graphTuple]
  have hspan : Ideal.span (Set.range graphCoords) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨⟨0⟩, hfirst⟩)
  have hnum (j : Fin (n + 1)) : graphCoords ⟨j.castSucc⟩ = numer j := by
    simp [graphCoords, graphTuple, Fin.cons_snoc_eq_snoc_cons, numer]
  have hlast : graphCoords ⟨Fin.last (n + 1)⟩ = evX Q := by
    simp [graphCoords, graphTuple, Fin.cons_snoc_eq_snoc_cons]
  have pol : chainSectionPolynomial a c =
      Q + (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i) + MvPolynomial.C c := by
    cases n <;> simp [Q, chainSectionPolynomial]
  have hp : p = graphCoords ⟨Fin.last (n + 1)⟩ +
      ∑ j : Fin (n + 1), (X ↘ S).appTop (l j) * graphCoords ⟨j.castSucc⟩ := by
    rw [hlast, Fin.sum_univ_succ]
    simp only [hnum, numer, l, Fin.cons_succ, Fin.cons_zero, mul_one, p, pol, evX,
      map_add, map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', coeff,
      CommRingCat.hom_comp, RingHom.comp_apply]
    abel
  obtain ⟨pre, comp⟩ := chartpull X (X ↘ S) graphCoords ⟨0⟩ hfirst hspan p hp
  refine ⟨pre, hZ, inferInstance, inferInstance, hdZ, chart, e, chartbase, chartcoord, ?_,
    forward_fac⟩
  simpa only [hnum] using comp

end WeilII

