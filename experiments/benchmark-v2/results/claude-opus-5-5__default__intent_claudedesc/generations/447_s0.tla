------------------------------ MODULE LetInstance ------------------------------
EXTENDS Naturals

(***************************************************************************)
(* An inner module that provides a "value plus one" operation.  It is      *)
(* instantiated locally inside a LET expression within the Next action,     *)
(* rather than at the top level of the enclosing module.                    *)
(***************************************************************************)
---------------------------------- MODULE Inc ----------------------------------
EXTENDS Naturals

PlusOne(v) == v + 1
================================================================================