module

public meta import WeilConjectures.Tactic.TransportExact

/-! # Congruence transport for components in a dependent local context -/

public meta section
open Lean Meta Elab Tactic in
/-- Transport across definitionally equal arguments of large functor expressions, keeping
the proof in its local context (which may contain dependent let-bound objects). -/
elab "transport_compactification_component " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let termProof ← elabTerm h none
  let sourceType ← instantiateMVars (← inferType termProof)
  let targetType ← instantiateMVars (← goal.getType)
  let typeHEq ← Mathlib.Tactic.TransportExact.heqProof (← IO.mkRef {}) sourceType targetType
  let typeEq := mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) sourceType targetType typeHEq
  let proof ← instantiateMVars (mkApp4 (mkConst ``Eq.mp [.zero]) sourceType targetType typeEq termProof)
  if proof.hasExprMVar then throwError "undetermined arguments in compactification component"
  goal.assign proof
  replaceMainGoal []
end

