import E3.Util.IO
import E3.Util.Expr
import E3.Engine.Preprocess
import SystemE.Smt

open Lean Meta


def numPropsAux : ℕ → List Expr → MetaM ℕ
| n, [] => return n
| n, h::t =>
  do if (← inferType (← inferType h)).isProp then numPropsAux (n+1) t else numPropsAux n t

def numProps : List Expr → MetaM ℕ :=
  numPropsAux 0

def WfCheckerAux (e : Expr) : MetaM String := do
  match ← SystemE.Smt.translateExpr e with
  | .error s => return s!"[E3/Wf] error: {s}"
  | .ok _ =>
    let neg ← isNegation e
    let nProps ← forallTelescopeReducing e (λ arr _ => numProps arr.toList)
    if !neg && nProps > 1 then
      throwError m!"[E3] error: formula contains too many implications, expected at most 1, got {nProps}"
    if neg && nProps > 2 then
        throwError m!"[E3] error: formula contains too many implications, expected at most 2, got {nProps}\n"
    else
      return "true"

def WfChecker (e : Expr) : IO Unit := do
  let e ← Prod.fst <$> MetaM.toIO (unfoldGeoAbbrevs e) E3Ctx (← E3State)
  let r ← Prod.fst <$> MetaM.toIO (WfCheckerAux e) E3Ctx (← E3State)
  if r != "true" then IO.println r
