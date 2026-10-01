module

public import Lean

/-!
# The `gap212` tag attribute

Marks a declaration as formalizing a named entity of the argument; a set of
declarations carrying one tag states that entity's content between them.

    @[gap212 "T001"]
    theorem my_result : True := trivial
-/

open Lean

public section

syntax (name := gap212Attr) "gap212 " str (str)? : attr

initialize registerBuiltinAttribute {
  name  := ``gap212Attr
  descr := "marks a declaration as formalizing a named entity of the argument"
  add   := fun _ _ _ => pure ()
}

end
