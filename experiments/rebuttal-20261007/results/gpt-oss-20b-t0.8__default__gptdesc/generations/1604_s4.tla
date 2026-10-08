```
---- MODULE ProcCallSpec ----
EXTENDS Naturals, Sequences

VARIABLES pc, stack, locals, outputStr

(* Initial state *)
Init ==
  /\ pc = "main"
  /\ stack = <<>>
  /\ locals = [p \in {"main","add","str"} |-> [v \in {} -> 0]]
  /\ outputStr = ""

(* Actions *)

MainCallAdd ==
  /\ pc = "main"
  /\ LET rec == [proc |-> "add", returnPc |-> "afterAdd", locals |-> locals] IN
       stack' = Append(stack, rec)
  /\ pc' = "add"
  /\ UNCHANGED outputStr

AddDone ==
  /\ pc = "add"
  /\ stack # <<>>
  /\ LET top == Head(stack) IN
        /\ top.proc = "add"
  /\ locals' = [locals EXCEPT !["add"]["result"] = 10]
  /\ stack' = Tail(stack)
  /\ pc' = top.returnPc
  /\ UNCHANGED outputStr

MainAfterAddCallStr ==
  /\ pc = "afterAdd"
  /\ LET rec == [proc |-> "str", returnPc |-> "afterStr", locals |-> locals] IN
       stack' = Append(stack, rec)
  /\ pc' = "str"

StrDone ==
  /\ pc = "str"
  /\ stack # <<>>
  /\ LET top == Head(stack) IN
        /\ top.proc = "str"
  /\ LET x == locals["add"]["result"] IN
        outputStr' = IF x = 10 THEN "10" ELSE ""
  /\ stack' = Tail(stack)
  /\ pc' = top.returnPc

AfterStrToDone ==
  /\ pc = "afterStr"
  /\ pc' = "done"
  /\ UNCHANGED <<stack, locals, outputStr>>

Next == MainCallAdd \/ AddDone \/ MainAfterAddCallStr \/ StrDone \/ AfterStrToDone

vars == {pc, stack, locals, outputStr}

(* Invariants *)
IntPassed ==
  (pc = "str") => locals["add"]["result"] = 10
OutputCorrect ==
  (pc = "done") => outputStr = "10"

Invs == IntPassed /\ OutputCorrect

Termination ==
  <> (pc = "done")

FairnessCondition == Fairness(Next)

Spec == Init /\ [][Next]_vars /\ FairnessCondition /\ Invs /\ Termination
```