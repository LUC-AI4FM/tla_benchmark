----------------------------- MODULE PlusCal_ProcCalls -----------------------------
EXTENDS Integers, Sequences

CONSTANTS Proc
ASSUME Proc # {}

(*
  Labels and stack-frame format used to emulate procedure calls/returns.
*)
Labels == {
  "start",
  "add_enter", "add_return", "afterAdd",
  "str_enter", "str_return", "afterStr",
  "Done"
}

StackFrame == [retpc : Labels]

VARIABLES
  pc,        \* per-process program counter
  stack,     \* per-process stack of activation records (for returns)
  a, b,      \* per-process arguments to addition procedure
  n,         \* per-process argument to string conversion procedure
  rvInt,     \* per-process integer return value (from add)
  rvStr,     \* per-process string return value (from to-string)
  outStr     \* final global output string

vars == << pc, stack, a, b, n, rvInt, rvStr, outStr >>

Init ==
  /\ pc = [ i \in Proc |-> "start" ]
  /\ stack = [ i \in Proc |-> << >> ]
  /\ a = [ i \in Proc |-> 0 ]
  /\ b = [ i \in Proc |-> 0 ]
  /\ n = [ i \in Proc |-> 0 ]
  /\ rvInt = [ i \in Proc |-> 0 ]
  /\ rvStr = [ i \in Proc |-> "" ]
  /\ outStr = ""

(*
  Process steps. The single logical PlusCal process is modeled here as a family
  of per-process actions (indexed by i in Proc), with an explicit stack of
  activation records holding the return PC.
*)

StartStep(i) ==
  /\ pc[i] = "start"
  /\ a' = [a EXCEPT ![i] = 3]
  /\ b' = [b EXCEPT ![i] = 7]
  /\ stack' = [stack EXCEPT ![i] = Append(@, [retpc |-> "afterAdd"])]
  /\ pc' = [pc EXCEPT ![i] = "add_enter"]
  /\ UNCHANGED << n, rvInt, rvStr, outStr >>

AddEnterStep(i) ==
  /\ pc[i] = "add_enter"
  /\ rvInt' = [rvInt EXCEPT ![i] = a[i] + b[i]]
  /\ pc' = [pc EXCEPT ![i] = "add_return"]
  /\ UNCHANGED << a, b, n, rvStr, outStr, stack >>

AddReturnStep(i) ==
  /\ pc[i] = "add_return"
  /\ Len(stack[i]) > 0
  /\ LET top == Head(stack[i]) IN
       /\ stack' = [stack EXCEPT ![i] = Tail(@)]
       /\ pc'    = [pc    EXCEPT ![i] = top.retpc]
  /\ UNCHANGED << a, b, n, rvInt, rvStr, outStr >>

AfterAddStep(i) ==
  /\ pc[i] = "afterAdd"
  /\ rvInt[i] = 10          \* assertion: the integer result is 10
  /\ n' = [n EXCEPT ![i] = rvInt[i]]
  /\ stack' = [stack EXCEPT ![i] = Append(@, [retpc |-> "afterStr"])]
  /\ pc' = [pc EXCEPT ![i] = "str_enter"]
  /\ UNCHANGED << a, b, rvInt, rvStr, outStr >>

StrEnterStep(i) ==
  /\ pc[i] = "str_enter"
  /\ n[i] = 10              \* assertion: integer passed to string conversion is 10
  /\ rvStr' = [rvStr EXCEPT ![i] = "10"]  \* models conversion result deterministically
  /\ pc'    = [pc    EXCEPT ![i] = "str_return"]
  /\ UNCHANGED << a, b, n, rvInt, stack, outStr >>

StrReturnStep(i) ==
  /\ pc[i] = "str_return"
  /\ Len(stack[i]) > 0
  /\ LET top == Head(stack[i]) IN
       /\ stack' = [stack EXCEPT ![i] = Tail(@)]
       /\ pc'    = [pc    EXCEPT ![i] = top.retpc]
  /\ UNCHANGED << a, b, n, rvInt, rvStr, outStr >>

AfterStrStep(i) ==
  /\ pc[i] = "afterStr"
  /\ outStr' = rvStr[i]
  /\ outStr' = "10"         \* assertion: final output string is "10"
  /\ pc' = [pc EXCEPT ![i] = "Done"]
  /\ UNCHANGED << a, b, n, rvInt, rvStr, stack >>

ProcStep(i) ==
  StartStep(i)
  \/ AddEnterStep(i)
  \/ AddReturnStep(i)
  \/ AfterAddStep(i)
  \/ StrEnterStep(i)
  \/ StrReturnStep(i)
  \/ AfterStrStep(i)

Next ==
  \E i \in Proc : ProcStep(i)

(*
  Safety invariants:
  - TypeOK ensures program-counter, stack, and variable types are preserved.
  - ArgIs10 holds whenever we are in/after the string conversion.
  - FinalOutIs10 holds when the process has finished.
*)
TypeOK ==
  /\ pc \in [Proc -> Labels]
  /\ stack \in [Proc -> Seq(StackFrame)]
  /\ a \in [Proc -> Int]
  /\ b \in [Proc -> Int]
  /\ n \in [Proc -> Int]
  /\ rvInt \in [Proc -> Int]
  /\ rvStr \in [Proc -> STRING]
  /\ outStr \in STRING

ArgIs10 ==
  \A i \in Proc :
    (pc[i] \in {"str_enter", "str_return", "afterStr", "Done"} => n[i] = 10)

FinalOutIs10 ==
  \A i \in Proc :
    (pc[i] = "Done" => outStr = "10")

Inv == TypeOK /\ ArgIs10 /\ FinalOutIs10

(*
  Liveness (termination-style) property:
  Eventually each process reaches Done, and eventually the final output is "10".
*)
Termination ==
  (\A i \in Proc : <> (pc[i] = "Done"))
  /\ <> (outStr = "10")

(*
  Fairness:
  The (single) PlusCal process is fair: each per-process action is weakly fair.
*)
Spec ==
  Init /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(ProcStep(i))

=============================================================================