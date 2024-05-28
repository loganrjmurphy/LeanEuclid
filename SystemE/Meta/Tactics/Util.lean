import Lean
import Batteries.Lean.Meta.UnusedNames


open Lean Elab Tactic Meta

namespace SystemE.Tactics

/--
Return if the weak head norm form of `e` is a conjunction.
-/
private def isConjunction (e : Expr) : MetaM Bool := do
  match (← whnf e).getAppFnArgs with
  | (``And, _) => return True
  | _ => return False

/--
Return if the weak head norm form of `e` is a disjunction.
-/
private def isDisjunction (e : Expr) : MetaM Bool := do
  match (← whnf e).getAppFnArgs with
  | (``Or, _) => return True
  | _ => return False

/--
Try to eliminate a conjunction `decl` in the local context.
-/
partial def elimConjunction (decl : LocalDecl) : TacticM Unit := do
  if ¬(← isConjunction decl.type) then
    return ()

  let left  ← getUnusedUserName `left
  let right ← getUnusedUserName `right
  evalTactic $ ← `(tactic| cases ($(mkIdent decl.userName)) with | intro $(mkIdent left) $(mkIdent right) => _)

  withMainContext do
    let ctx ← getLCtx
    if let some l := ctx.findFromUserName? left then
      elimConjunction l
    if let some r := ctx.findFromUserName? right then
      elimConjunction r

/--
Try to eliminate a disjunction `decl` in the local context.
-/
partial def elimDisjunction (decl : LocalDecl) : TacticM Unit := do
  if ¬(← isDisjunction decl.type) then
    return ()

  let left  ← getUnusedUserName `left
  let right ← getUnusedUserName `right
  evalTactic $ ← `(tactic| cases ($(mkIdent decl.userName)) with | inl $(mkIdent left) => _ | inr $(mkIdent right) => _)

  withMainContext do
    let ctx ← getLCtx
    if let some l := ctx.findFromUserName? left then
      elimDisjunction l
    if let some r := ctx.findFromUserName? right then
      elimDisjunction r

/--
Destruct all conjunctions in the local context.
-/
def elimAllConjunctions : TacticM Unit :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      elimConjunction decl

/--
Destruct all conjunctions in the local context.
-/
def elimAllDisjunctions : TacticM Unit :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      elimDisjunction decl

syntax "split_ors" : tactic

elab "split_ors" : tactic => elimAllDisjunctions

def pretty (e : Expr) : MetaM Format := do
    let s ← Tactic.TryThis.delabToRefinableSyntax e
    let f ← PrettyPrinter.ppCategory `term s
    pure f

def traceUnsolved (unsolved : List Format) : TacticM Unit := do
    let unsolved := ",".intercalate (unsolved.map Format.pretty)
    logInfo s!"unsolved goals: {unsolved}"

end SystemE.Tactics
