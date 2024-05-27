import Lean
import SystemE.Meta.Tactics.Util


open Lean Elab Tactic Meta

namespace SystemE.Tactics

/--
The `euclid_intros` tactic is similar to `intros`, but it also destructs conjunctions.
-/
def EuclidIntros : TacticM Unit := do
  Lean.Elab.Tactic.withMainContext do
    forallTelescopeReducing (← getMainTarget) fun fvars _ => do
      let ctx ← getLCtx
      for fvar in fvars do
        let decl := ctx.getFVar! fvar
        -- Run `intro`.
        liftMetaTactic fun g => do
          let (_, g') ← g.intro decl.userName
          return [g']
        -- Destruct conjunctions.
        elimConjunction decl

syntax "euclid_intros" : tactic

elab "euclid_intros" : tactic => SystemE.Tactics.EuclidIntros

end SystemE.Tactics
