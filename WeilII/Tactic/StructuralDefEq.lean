module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.CongrTheorems

/-! # Structural congruence for large categorical composites

The tactics descend through common application heads, expanding local abbreviations only
where their heads differ. As in the pinned WeilConjectures `Tactic/TransportExact.lean`,
heterogeneous congruence supplies the transports. Keeping composite functor objects in their
original form avoids reducing the derived pullbacks.
-/

public meta section

namespace WeilII.Tactic.StructuralDefEq

open Lean Meta Elab Tactic

/-- Compare matching applications before reducing functor objects. This retains the original
implicit endpoints of morphisms throughout the congruence proof. -/
private partial def structuralHEq (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
    MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let make : MetaM Expr := do
    if (← isProof a) && (← isProof b) then
      return mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b
    unless a.hasLooseBVars || b.hasLooseBVars do
      if let .letE _ _ v t _ := a then return ← structuralHEq cache (t.instantiate1 v) b
      if let .letE _ _ v t _ := b then return ← structuralHEq cache a (t.instantiate1 v)
    let a' := a.headBeta
    let b' := b.headBeta
    if a' != a || b' != b then return ← structuralHEq cache a' b'
    let f := a.getAppFn
    let g := b.getAppFn
    if f != g then
      if f.isFVar then
        if let some v := (← f.fvarId!.getDecl).value? then
          return ← structuralHEq cache (mkAppN v a.getAppArgs) b
      if g.isFVar then
        if let some v := (← g.fvarId!.getDecl).value? then
          return ← structuralHEq cache a (mkAppN v b.getAppArgs)
    let xs := a.getAppArgs
    let ys := b.getAppArgs
    if f == g && xs.size == ys.size && xs.size > 0 then
      let hc ← match f with
        | .const n us => do
          match ← mkHCongrWithArityForConst? n us xs.size with
          | some h => pure h
          | none => mkHCongrWithArity f xs.size
        | _ => mkHCongrWithArity f xs.size
      let mut args := #[]
      for i in [:xs.size] do
        let x := xs[i]!
        let y := ys[i]!
        let h ← if hc.argKinds[i]? == some .eq then do
          if x == y then mkEqRefl x else do
            let α ← inferType x
            pure (mkApp4 (mkConst ``eq_of_heq [← getLevel α]) α x y (← structuralHEq cache x y))
          else structuralHEq cache x y
        args := args.push x |>.push y |>.push h
      return mkAppN hc.proof args
    return ← mkHEqRefl a
  let h ← make
  cache.modify (·.insert (a, b) h)
  return h

/-- Transport a proof between definitionally equal propositions by structural congruence. -/
elab "structural_exact " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let p ← instantiateMVars (← elabTerm h none)
  let A ← instantiateMVars (← inferType p)
  let B ← instantiateMVars (← goal.getType)
  let e ← structuralHEq (← IO.mkRef {}) A B
  let eq := mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B e
  goal.assign (mkApp4 (mkConst ``Eq.mp [.zero]) A B eq p)
  replaceMainGoal []

/-- Prove a definitional equality by congruence down to reflexivity and proof irrelevance. -/
elab "structural_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let B ← instantiateMVars (← goal.getType)
  let some (α, l, r) := B.eq? | throwError "expected an equality"
  let h ← structuralHEq (← IO.mkRef {}) l r
  goal.assign (mkApp4 (mkConst ``eq_of_heq [← getLevel α]) α l r h)
  replaceMainGoal []

end WeilII.Tactic.StructuralDefEq
