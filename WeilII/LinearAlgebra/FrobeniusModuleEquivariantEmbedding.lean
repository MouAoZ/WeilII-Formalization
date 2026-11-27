module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor
import Mathlib.RingTheory.Flat.Basic

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- Existence of a linear injection commuting with the two Frobenius actions. -/
@[expose] public def Embeds (T W : FrobeniusModule K) : Prop :=
  ∃ u : T.carrier →ₗ[K] W.carrier,
    Function.Injective u ∧ ∀ x, u (T.frobenius x) = W.frobenius (u x)

/-- Tensor an equivariant embedding on the right and then include the result in a further
Frobenius module, as in the Künneth induction on page 2 of Zhang. -/
public theorem Embeds.rTensor_trans {T H V W : FrobeniusModule K}
    (h : T.Embeds H) (k : (H.tensor V).Embeds W) : (T.tensor V).Embeds W := by
  obtain ⟨u, hu, fu⟩ := h
  obtain ⟨j, hj, fj⟩ := k
  let t := u.rTensor V.carrier
  have ht : Function.Injective t := Module.Flat.rTensor_preserves_injective_linearMap u hu
  have comm : u.comp T.frobeniusEnd = H.frobeniusEnd.comp u := LinearMap.ext fu
  have ft : t.comp (T.tensor V).frobeniusEnd = (H.tensor V).frobeniusEnd.comp t := by
    rw [frobeniusEnd_tensor, frobeniusEnd_tensor]
    exact (LinearMap.rTensor_comp_map _ _ _ _).trans
      ((congrArg (fun f ↦ TensorProduct.map f V.frobeniusEnd) comm).trans
        (LinearMap.map_comp_rTensor _ _ _ _).symm)
  exact ⟨j.comp t, hj.comp ht, fun x ↦ (congrArg j (DFunLike.congr_fun ft x)).trans (fj _)⟩

end FrobeniusModule
