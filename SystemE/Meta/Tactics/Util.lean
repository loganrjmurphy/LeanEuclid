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

/- Modified version of "TryThis" widget (ref) -/
@[widget] def euclidApplyWidget : Widget.UserWidgetDefinition where
  name := "Reasoning Gaps (euclid_apply)"
  javascript := "
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)
  function onClick() {
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range: props.range, newText: props.toReplace}] }
    })
  }
  return e('div', {className: 'ml1'}, e('pre', {className: 'font-code pre-wrap'}, [
    'Could not prove: ',
    e('a', {onClick, className: 'link pointer dim', title: 'Apply suggestion'}, props.toReplace),
    props.info
  ]))
}"

/- Modified version of "Try this" -/
private def addUnsolved (ref : Syntax) (bare : String) (tac : String)
    (origSpan? : Option Syntax := none)
    (extraMsg : String := "") : MetaM Unit := do
  if let some range := (origSpan?.getD ref).getRange? then
    let map ← getFileMap
    let stxRange := ref.getRange?.getD range
    let stxRange :=
    { start := map.lineStart (map.toPosition stxRange.start).line
      stop := map.lineStart ((map.toPosition stxRange.stop).line + 1) }
    let range := map.utf8RangeToLspRange range
    let json := Json.mkObj [("suggestion", bare), ("toReplace", tac), ("range", toJson range), ("info", extraMsg)]
    Widget.saveWidgetInfo ``euclidApplyWidget json (.ofRange stxRange)

def pretty (e : Expr) : MetaM Format := do
    let s ← Tactic.TryThis.delabToRefinableSyntax e
    let f ← PrettyPrinter.ppCategory `term s
    pure f

def traceUnsolvedToWidget (unsolved : List Format) : TacticM Unit := do
    let bare := ",".intercalate (unsolved.map Format.pretty)
    let text := unsolved.map (fun x => "have : " ++ Format.pretty x ++ ":= by {sorry}")
    let text := "; ".intercalate text
    addUnsolved (← getRef) bare text (origSpan? := ← getRef)

end SystemE.Tactics
