import Lean
import Smt.Solver
import SystemE.Meta.Smt.EuclidTheory
import SystemE.Meta.Smt.Translator

set_option autoImplicit false
open Lean Elab Tactic Meta Smt Solver SystemE.Smt

register_option systemE.trace : Bool := {
  defValue := false
  descr := "Trace the SMT-LIBv2 query generated from the proof context."
}

register_option systemE.solverTime : Nat := {
  defValue := 180
  descr := "Number of seconds to allow each solver (z3, cvc5) to fill reasoning gaps (default: 180)."
}

def getTimeOption : MetaM Nat := do
  match systemE.solverTime.get? (← getOptions) with
  | none => return 180
  | some x => return x

def getTraceOption : MetaM Bool := do
  match (← getOptions).getBool `systemE.trace with
  | true => return true
  | _ => return false

namespace SystemE.Tactics.Translation

/- Translate an `EConst` to a declaration of a constant -/
private def fromEConst : EConst → Smt.Command
| ⟨name, sort⟩ => Smt.Command.declare name (Smt.Term.symbolT sort.toString)

/- Translate an `EAssertion` to an SMT assertion -/
private def fromEAssertion (e : EAssertion) : Smt.Command :=
  e |> toString |> Smt.Term.literalT |> Smt.Command.assert

/- Translate the entire ESMT context to a list of SMT commands -/
def fromEsmt : Esmt → List Smt.Command
| ⟨consts, _, asserts, _⟩ =>
  (consts.map fromEConst) ++ (asserts.map fromEAssertion) |>.toList

/- Unsound axiom we use to admit results from the solvers
   Dangerous!
 -/
axiom SMT_VERIF (P : Prop) : P

/-
  Close the current goal using the above axiom.
  It is crucial to ensure that this is only invoked when an `unsat` result is returned
-/
def closeWithAxiom (g : MVarId) : TacticM Unit := do
  let _ ← evalTacticAt (← `(tactic| apply SMT_VERIF)) g

/-
  Use `Sorry` to close the goal.
-/
def emitGoalAndCloseWithSorry (g : MVarId) : MetaM Unit := do
  let e ← instantiateMVars (← g.getType)
  logError m!"Could not prove: {e}"
  admitGoal g

/-- Given the chosen  solver and current Esmt context, check whether it is satisfiable-/
def evalSmt (Γ : Esmt) : TacticM Result := do
  -- Choose the background theory depending on the solver, they differ only in the patterns used
  let cmds : List Smt.Command := euclidTheory ++ fromEsmt Γ
  if ← getTraceOption then
    logInfo $ (Command.cmdsAsQuery cmds.reverse) ++ "\n(check-sat)"
  let query := addCommands cmds *> checkSat
  let solverState ← Smt.Solver.create (← getTimeOption)
  let result ← (StateT.run' query solverState : MetaM _)
  if ← getTraceOption then
    logInfo s!"{result}"
  return result

end SystemE.Tactics.Translation
