------------------------------------------- MODULE PlusCalSpec -------------------------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES pc, stack, locals

(*--------------------------------------------------------------------
   Types and helper definitions
 *--------------------------------------------------------------------*)
Rec == [proc : String,
        args : Seq(Int),
        retVar : String,
        nextPC : String]

Value == Int \/ String

(* Domain of the local variable mapping *)
LocalNames == {"addResult", "stringResult"}

(*--------------------------------------------------------------------
   Initial state
 *--------------------------------------------------------------------*)
Init ==
  /\ pc = "start"
  /\ stack = <<>>
  /\ locals = [x \in LocalNames |-> IF x = "addResult" THEN 0 ELSE "" ]

(*--------------------------------------------------------------------
   Transitions
 *--------------------------------------------------------------------*)

(* Call the addition procedure *)
CallAdd ==
  /\ pc = "start"
  /\ stack' = Append(stack,
                    [proc |-> "Add",
                     args |-> <<5,5>>,
                     retVar |-> "addResult",
                     nextPC |-> "afterAdd"])
  /\ pc' = "callAdd"

(* Execute the addition procedure *)
ExecAdd ==
  /\ pc = "callAdd"
  /\ Len(stack) > 0
  /\ RecTop == Last(stack)
  /\ RecTop.proc = "Add"
  /\ locals' = [locals EXCEPT ![RecTop.retVar] =
                RecTop.args[1] + RecTop.args[2]]
  /\ stack' = SubSeq(stack, 1, Len(stack)-1)      (* pop *)
  /\ pc' = "afterAdd"

(* Call the integer-to-string procedure *)
CallIntToString ==
  /\ pc = "afterAdd"
  /\ locals["addResult"] = 10
  /\ stack' = Append(stack,
                    [proc |-> "IntToString",
                     args |-> <<locals["addResult"]>>,
                     retVar |-> "stringResult",
                     nextPC |-> "afterIntToString"])
  /\ pc' = "callIntToString"

(* Execute the integer-to-string procedure *)
ExecIntToString ==
  /\ pc = "callIntToString"
  /\ Len(stack) > 0
  /\ RecTop == Last(stack)
  /\ RecTop.proc = "IntToString"
  /\ locals' = [locals EXCEPT ![RecTop.retVar] = "10"]
  /\ stack' = SubSeq(stack, 1, Len(stack)-1)      (* pop *)
  /\ pc' = "afterIntToString"

(* Transition to the final state *)
Finish ==
  /\ pc = "afterIntToString"
  /\ pc' = "done"

Next == CallAdd \/ ExecAdd \/ CallIntToString \/ ExecIntToString \/ Finish

(*--------------------------------------------------------------------
   Invariants
 *--------------------------------------------------------------------*)
InvArgIsTen ==
  [] (pc = "callIntToString" => Len(stack) > 0 /\ Last(stack).args[1] = 10)

InvResultIsTen ==
  [] (pc = "done" => locals["stringResult"] = "10")

(*--------------------------------------------------------------------
   Liveness property
 *--------------------------------------------------------------------*)
Termination == <> (pc = "done")

(*--------------------------------------------------------------------
   Specification
 *--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc,stack,locals>> /\ WF_Proc(Next) /\ Termination /\ InvArgIsTen /\ InvResultIsTen

=============================================================================