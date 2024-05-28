import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

/--
A segment is defined by two endpoints.
-/
inductive Segment
| endpoints (a b : Point)

namespace Segment
opaque length : Segment → ℝ

instance : Coe Segment ℝ := ⟨length⟩

end Segment

open Lean PrettyPrinter

syntax "(" term "─" term ")": term

macro_rules
| `(($t:term ─ $s:term)) => `(Segment.endpoints $t $s)

@[app_unexpander Segment.endpoints]
def unexpand_endpoints : Unexpander
| `($_ $t $s) => `(($t ─ $s))
| _ => throw ()

/- Override the notation for absolute/magnitude used by Abs typeclass, i.e., | ⬝ |, -/
macro:max (priority := high) atomic("|" noWs) a:term noWs "|"  : term => `(Segment.length $a)

@[app_unexpander Segment.length]
def unexpand_length : Lean.PrettyPrinter.Unexpander
| `($_ $i:ident) => `(|$i:ident|)
| `($_ ($t:term ─ $s:term)) => `(|($t:term─$s:term)|)
| _ => throw ()
