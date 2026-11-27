module

public import WeilConjectures.CategoryTheory.Abelian.PowShift

/-!
# Ordinary quotient towers for a complete monomorphism
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilII

/-- If one minus the shift by a monomorphism is invertible on the countable power,
the projections to its positive-power cokernels form a limit cone whenever their
product is epi. The inverse of one minus shift corrects simultaneous local lifts
of compatible residue classes to a single map into the original object. -/
public theorem isLimit_quotientCone_of_isIso_sub_powShift
    {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape (Discrete ℕ) C]
    {A : C} (e : End A) [Mono e.asHom] [IsIso (𝟙 _ - powShift e.asHom)]
    {D : ℕᵒᵖ ⥤ C} [HasLimit D] (p : (Functor.const ℕᵒᵖ).obj A ⟶ D)
    (hq : ∀ n : ℕ, ∃ w : (e ^ (n + 1)).asHom ≫ p.app (op n) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (p.app (op n)) w)))
    (hp : Epi (Limits.Pi.map (f := fun _ : ℕ ↦ A) (fun n ↦ p.app (op n)))) :
    Nonempty (IsLimit (Cone.mk A p)) := by
  classical
  let a (n : ℕ) := (e ^ (n + 1)).asHom
  have step (n : ℕ) : a (n + 1) = e.asHom ≫ a n := by
    simp only [a, pow_succ e (n + 1), End.mul_asHom]
  have ma (n : ℕ) : Mono (a n) := by
    induction n with
    | zero => simpa [a] using (inferInstance : Mono e.asHom)
    | succ n ih => rw [step]; infer_instance
  choose w hw using hq
  have factor {B : C} (n : ℕ) (x : B ⟶ A) (hx : x ≫ p.app (op n) = 0) :
      ∃ y, y ≫ a n = x :=
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (a n) (p.app (op n)) (w n)) (hw n).some).lift' x hx
  let f := limit.lift D (Cone.mk A p)
  have fac (n : ℕ) : f ≫ limit.π D (op n) = p.app (op n) := limit.lift_π _ _
  let shiftDiff := 𝟙 _ - powShift e.asHom
  have coord {B : C} (t : B ⟶ ∏ᶜ fun _ : ℕ ↦ A) (n : ℕ) :
      (t ≫ shiftDiff) ≫ Pi.π _ n =
        t ≫ Pi.π _ n - (t ≫ Pi.π _ (n + 1)) ≫ e.asHom := by
    simp [shiftDiff, Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub]
  -- A map killed by all projections is divisible compatibly by every power.
  have : Mono f := by
    refine Preadditive.mono_of_cancel_zero _ fun {B} x hx ↦ ?_
    have hz (n : ℕ) : x ≫ p.app (op n) = 0 := by
      rw [← fac, ← Category.assoc, hx, zero_comp]
    choose b hb using fun n ↦ factor n x (hz n)
    have hshift : Pi.lift b ≫ shiftDiff = 0 := by
      apply Pi.hom_ext
      intro n
      rw [coord, zero_comp, Pi.lift_comp_π, Pi.lift_comp_π, sub_eq_zero, ← cancel_mono (a n),
        Category.assoc, ← step, hb, hb]
    have hzero : Pi.lift b = 0 := zero_of_comp_mono shiftDiff hshift
    rw [← hb 0, ← Pi.lift_comp_π b 0, hzero, zero_comp, zero_comp]
  have : Epi f := by
    rw [epi_iff_surjective_up_to_refinements]
    intro B x
    -- Lift all components along a single epimorphic refinement.
    obtain ⟨T, r, hr, lifts, hl⟩ := surjective_up_to_refinements_of_epi
      (Limits.Pi.map (f := fun _ : ℕ ↦ A) (fun n ↦ p.app (op n)))
      (Pi.lift fun n ↦ x ≫ limit.π D (op n))
    let b (n : ℕ) := lifts ≫ Pi.π _ n
    have hb (n : ℕ) : b n ≫ p.app (op n) = r ≫ x ≫ limit.π D (op n) := by
      simpa [b, Category.assoc] using hl.symm =≫ Pi.π _ n
    have hd (n : ℕ) : (b n - b (n + 1)) ≫ p.app (op n) = 0 := by
      let i : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
      have hi : p.app (op (n + 1)) ≫ D.map i = p.app (op n) := (Cone.mk A p).w i
      rw [Preadditive.sub_comp, sub_eq_zero, hb, ← hi, ← Category.assoc (b _), hb,
        Category.assoc, Category.assoc, limit.w]
    -- Divide adjacent differences by the relevant power, then solve for the corrections.
    choose k hk using fun n ↦ factor n _ (hd n)
    let t := Pi.lift k ≫ inv shiftDiff
    have ht (n : ℕ) : t ≫ Pi.π _ n - (t ≫ Pi.π _ (n + 1)) ≫ e.asHom = k n := by
      rw [← coord]
      simp [t, Category.assoc]
    let c (n : ℕ) := b n - (t ≫ Pi.π _ n) ≫ a n
    have hc (n : ℕ) : c n = c (n + 1) := by
      have h := ht n =≫ a n
      rw [Preadditive.sub_comp, Category.assoc (t ≫ _), ← step, hk] at h
      exact sub_eq_sub_iff_sub_eq_sub.mp h.symm
    have hc₀ (n : ℕ) : c 0 = c n := by
      induction n with
      | zero => rfl
      | succ n ih => exact ih.trans (hc n)
    refine ⟨T, r, hr, c 0, limit.hom_ext fun ⟨n⟩ ↦ ?_⟩
    rw [Category.assoc, Category.assoc, fac, hc₀ n, ← hb]
    simp [c, a, Preadditive.sub_comp, Category.assoc, w]
  exact (limit.isLimit D).nonempty_isLimit_iff_isIso_lift.mpr (isIso_of_mono_of_epi f)

end WeilII
