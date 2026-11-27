module

public meta import WeilConjectures.Tactic.FirstOrderApply
public meta import Lean.Meta.CongrTheorems

/-! # Congruence for bounded pullback and shriek components

The bounded pullbacks lift the derived pullbacks on underlying schemes. Expand those lifts
before comparing their arguments. At the underlying scheme or map projection, reduction
identifies the two terms directly. A shriek functor comparison instead uses the supplied
equality on its edge. As in `StructuralDefEq`, keep the endpoints of each heterogeneous
congruence in their original form.
-/

public meta section

namespace WeilII.Tactic.SchemeComponentCongruence

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

private def isShriekFunctor (e : Expr) : Bool :=
  e.isAppOfArity `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriek 15

private partial def componentHEq (expandSquare : Bool) (hints : Array Expr)
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
    MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let make : MetaM Expr := do
    if (← isProof a) && (← isProof b) then
      return mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b
    unless a.hasLooseBVars || b.hasLooseBVars do
      if let .letE _ _ v t _ := a then return ← componentHEq expandSquare hints cache (t.instantiate1 v) b
      if let .letE _ _ v t _ := b then return ← componentHEq expandSquare hints cache a (t.instantiate1 v)
    let a' := a.headBeta
    let b' := b.headBeta
    if a' != a || b' != b then return ← componentHEq expandSquare hints cache a' b'
    let f := a.getAppFn
    let g := b.getAppFn
    -- The shriek functor is identified by the supplied equality on its slice arrow.
    if isShriekFunctor a && isShriekFunctor b then
      for h in hints do
        let some (_, l, r) := (← whnfR (← inferType h)).eq? | continue
        unless isShriekFunctor l && isShriekFunctor r do continue
        for (x, y, rev) in [(l, r, false), (r, l, true)] do
          if (← isDefEq a.getAppArgs.back! x.getAppArgs.back!) &&
              (← isDefEq b.getAppArgs.back! y.getAppArgs.back!) then
            return ← mkHEqOfEq (← if rev then mkEqSymm h else pure h)
    if !expandSquare && (a.isAppOf `CategoryTheory.Functor.obj || b.isAppOf `CategoryTheory.Functor.obj) then
      let a' ← Mathlib.Tactic.FirstOrderApply.normObj a
      let b' ← Mathlib.Tactic.FirstOrderApply.normObj b
      if a' != a || b' != b then return ← componentHEq expandSquare hints cache a' b'
    let unfolds (e : Expr) :=
      e.isAppOf `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarOfMap ||
      e.isAppOf `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar ||
      (expandSquare && (e.isAppOf `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapSquareIso ||
        e.isAppOf `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapComp))
    if unfolds a || unfolds b then
      let a' ← if unfolds a then pure ((← unfoldDefinition? a).getD a) else pure a
      let b' ← if unfolds b then pure ((← unfoldDefinition? b).getD b) else pure b
      if a' != a || b' != b then return ← componentHEq expandSquare hints cache a' b'
    -- The underlying schemes and maps agree even when their slice objects differ.
    if a.isAppOf `CategoryTheory.Over.left || b.isAppOf `CategoryTheory.Over.left ||
        a.isAppOf `CategoryTheory.Over.Hom.left || b.isAppOf `CategoryTheory.Over.Hom.left then
      return ← mkHEqRefl a
    if f != g then
      if f.isFVar then
        if let some v := (← f.fvarId!.getDecl).value? then
          return ← componentHEq expandSquare hints cache (mkAppN v a.getAppArgs) b
      if g.isFVar then
        if let some v := (← g.fvarId!.getDecl).value? then
          return ← componentHEq expandSquare hints cache a (mkAppN v b.getAppArgs)
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
            pure (mkApp4 (mkConst ``eq_of_heq [← getLevel α]) α x y (← componentHEq expandSquare hints cache x y))
          else componentHEq expandSquare hints cache x y
        args := args.push x |>.push y |>.push h
      return mkAppN hc.proof args
    return ← mkHEqRefl a
  let h ← make
  cache.modify (·.insert (a, b) h)
  return h

/-- Transport a component identity using the given equalities of shriek functors. -/
elab "scheme_component_exact " h:term " using " hints:ident,+ : tactic => withMainContext do
  let goal ← getMainGoal
  let p ← instantiateMVars (← elabTerm h none)
  let facts ← hints.getElems.mapM fun hint => elabTerm hint none
  let A ← instantiateMVars (← inferType p)
  let B ← instantiateMVars (← goal.getType)
  let e ← componentHEq false facts (← IO.mkRef {}) A B
  let eq := mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B e
  goal.assign (mkApp4 (mkConst ``Eq.mp [.zero]) A B eq p)
  replaceMainGoal []

/-- Compare the two presentations of a pullback-square component by unfolding its
composition constraints and reducing the underlying scheme projections. -/
elab "scheme_pullback_component_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let B ← instantiateMVars (← goal.getType)
  let some (α, l, r) := B.eq? | throwError "expected an equality"
  let h ← componentHEq true #[] (← IO.mkRef {}) l r
  goal.assign (mkApp4 (mkConst ``eq_of_heq [← getLevel α]) α l r h)
  replaceMainGoal []

end WeilII.Tactic.SchemeComponentCongruence
