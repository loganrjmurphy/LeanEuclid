-- -- import Lean.Elab.Command
-- import Lean
-- import Std
-- import SystemE.Tactics.Util

-- open Lean Elab Term Command Meta SystemE.Tactics

-- syntax (name := addInst) "addInst" str : attr
-- initialize registerTraceClass `addInst

-- syntax (name := addFormal) "addFormal" str ident : attr

-- initialize registerTraceClass `addFormal

-- structure FormalDatum where
--   name : String
--   english : String
--   formalExpr : String
--   deriving Inhabited, Repr, BEq, Hashable

-- initialize formalDataExtension :
--     SimplePersistentEnvExtension (FormalDatum) (HashSet FormalDatum) ←
--   registerSimplePersistentEnvExtension {
--     name := `formalDataExtensionAdder
--     addImportedFn := fun arrays =>
--       arrays.foldl (init := ∅) fun acc as =>
--         as.foldl (init := acc) fun acc' a => acc'.insert  a
--     addEntryFn    := fun s x => s.insert x
--     toArrayFn     := fun es => es.toArray
--   }


-- def update_aux (map : HashMap String (List String)) (entry :String × String) : HashMap String (List String) :=
--  match map[entry.1] with
--  | none => map.insert entry.1 [entry.2]
--  | some l => map.insert entry.1 (entry.2::l)

-- initialize formalInstanceExtension :
--     SimplePersistentEnvExtension (String × String) (HashMap String (List String)) ←
--   registerSimplePersistentEnvExtension {
--     name := `formalInstanceExtensionAdder
--     addImportedFn := fun arrays =>
--       arrays.foldl (init := ∅) fun acc as =>
--         as.foldl (init := acc) update_aux
--     addEntryFn    := fun s x => update_aux s x
--     toArrayFn     := fun es => es.toArray
--   }


-- def findValueFromConstDeclName (declName : Name) : MetaM Expr := do
--   match (← getEnv).find? declName with
--   | some (ConstantInfo.defnInfo x) => return x.value
--   | _ => throwError "unrecognized declname {declName}; ensure it is declared as `def` in the current namespace"

-- def findTypeFromConstDeclName (declName : Name) : MetaM Expr := do
--   match (← getEnv).find? declName with
--   | some (ConstantInfo.thmInfo x) => return x.type
--   | _ => throwError "unrecognized declname {declName} ; ensure it is declared as `Theorem`"

-- initialize registerBuiltinAttribute {
--   name := `addInst
--   descr := "Attribute for adding english/lean formalization example."
--   applicationTime := .afterTypeChecking
--   add := fun declName stx _ => do
--     let `(attr| addInst $s) := stx
--       | throwError "error on `@[addInst]` attribute {stx}"
--     MetaM.run' do
--           let formalStatement ← findTypeFromConstDeclName declName
--           let pf ← pretty formalStatement
--           modifyEnv fun env =>
--              formalInstanceExtension.addEntry env (s.getString,  (pf.pretty  (w := 10000)))
--   }

-- initialize registerBuiltinAttribute {
--   name := `addFormal
--   descr := "Attribute for adding lean formalization to dataset."
--   applicationTime := .afterTypeChecking
--   add := fun declName stx _ => do
--     let `(attr| addFormal $n $englishDecl) := stx
--       | throwError "error on `@[addFormal]` attribute {stx}"
--     MetaM.run' do
--           let ns ← getCurrNamespace
--           let englishStatement ← findValueFromConstDeclName (.str ns englishDecl.getId.toString)
--           let formalStatement ← findTypeFromConstDeclName declName
--           let pe ← pretty englishStatement
--           let pf ← pretty formalStatement
--           modifyEnv fun env =>
--              formalDataExtension.addEntry env {name := n.getString, english := pe.pretty (w := 10000), formalExpr := pf.pretty  (w := 10000)}
--   }

-- register_option Formalization.path : String := {
--   defValue := ""
--   descr := "Directory in which to store Formalization."
-- }

-- -- elab "PrintFormalizations" : command => do
-- --   let x := formalDataExtension.getState (← getEnv)
-- --   x.forM (λ s x => do dbg_trace s)
