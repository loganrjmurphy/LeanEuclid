/-- Miscellaneous utility functions for translating strings into JSON objects -/

def quoted {α : Type} [ToString α] : α → String := (s!"\"{.}\"")

def wrapObject (str : String) : String := s!"\{{str}}"

def formatPermutationJson (raw guarded test ground : String) : String :=
     let wrap_test := wrapObject test
     let wrap_ground := wrapObject ground
     wrapObject s!"\"ground\" : \"{raw}\",\n\"guarded_test\" : \"{(guarded)}\",\n\"guarded_test_names\" : {wrap_test},\n\"ground_names\" : {wrap_ground}"
