-- import SystemE.Tactics.Formalization.AddFormal

-- open Lean



-- def getFormalizationDirectory : Elab.Command.CommandElabM String := do
--  match (← getOptions).getString `Formalization.path with
--  | "" => throwError "no directory specified for writing formalization instances; please use `set_option Formalization.path <dir>`"
--  | d => return d


-- namespace FormalDatum

-- def toString : FormalDatum → String
-- | ⟨nm, eng, fml⟩ => s!"\"{nm}\" : \{ \"english\" : {eng},\"formal\"  : \"{fml}\"}"

-- --
-- instance : ToString FormalDatum := ⟨toString⟩
-- end FormalDatum

-- def helper (x: String × (List String)) : String :=
-- match x with
-- | ⟨key, val⟩ =>
--   let val := val.map (λ x => s!"\"{x}\"")
--   s!"\"{key}\": {val}"

-- def writeEntries (h : IO.FS.Handle) : List (String × (List String)) → IO Unit
-- | x::[] => h.putStrLn $ (helper x) ++ "\n}"
-- | x::y => do h.putStrLn $ (helper x) ++ "," ; writeEntries h y
-- | [] => return

-- -- todo: Avoid writing newlines to json
-- syntax "exportFormalizations" : command
-- elab "exportFormalizations" : command => do
--   let dir ← getFormalizationDirectory
--   let data := HashMap.toList $ formalInstanceExtension.getState (← getEnv)
--   let h ← IO.FS.Handle.mk dir IO.FS.Mode.write
--   h.putStrLn "{"
--   writeEntries h data
--   -- for entry in data do
--   --   let _ ←  h.putStrLn s!"\"{entry.name}\" : \{ \"english\" : {entry.english},\"formal\"  : \"{entry.formalExpr}\"}"
--   return ()
