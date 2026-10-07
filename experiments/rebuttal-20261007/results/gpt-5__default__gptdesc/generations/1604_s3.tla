----------------------------- MODULE AddThenStr -----------------------------
EXTENDS Integers, Sequences

(*
  A TLA+ specification emulating a PlusCal program with one fair process that
  calls two procedures in sequence: an addition procedure and an int-to-string
  procedure. Procedure calls are modeled with a per-process program counter,
  per-process local-variable functions, and a stack of activation records.
*)

CONSTANTS

(*
  One logical process, identified as 0.
*)
ProcSet == {0}

(*
  Control-flow labels used in the single process and inside procedures.
*)
Labels ==
  {"start", "add_0", "ret_add", "afterAdd",
   "str_0", "ret_str", "afterStr", "Done"}

(*
  Restrict strings to those used in the model.
*)
StrSet == {"", "10", "not10"}

(*
  Activation record (stack frame) shapes.
*)
AddFrame == [kind: {"Add"}, retpc: Labels, a: Int, b: Int, res: Int]
StrFrame == [kind: {"Str"}, retpc: Labels, i: Int, out: StrSet]
Frame    == AddFrame \cup StrFrame

(*
  Helpers for stack manipulation (defined on non-empty sequences).
*)
Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)

VARIABLES
  pc,        \* per-process program counter: [ProcSet -> Labels]
  stack,     \* per-process stack of activation records: [ProcSet -> Seq(Frame)]
  add_a,     \* per-process locals for Add procedure
  add_b,
  add_res,
  itos_i,    \* per-process locals for Str (int-to-string) procedure
  itos_out,
  tmp,       \* per-process temp to hold Add result before Str call
  out        \* per-process final output string

vars == << pc, stack, add_a, add_b, add_res, itos_i, itos_out, tmp, out >>

TypeOK ==
  /\ pc \in [ProcSet -> Labels]
  /\ stack \in [ProcSet -> Seq(Frame)]
  /\ add_a \in [ProcSet -> Int]
  /\ add_b \in [ProcSet -> Int]
  /\ add_res \in [ProcSet -> Int]
  /\ itos_i \in [ProcSet -> Int]
  /\ itos_out \in [ProcSet -> StrSet]
  /\ tmp \in [ProcSet -> Int]
  /\ out \in [ProcSet -> StrSet]

Init ==
  /\ pc = [p \in ProcSet |-> "start"]
  /\ stack = [p \in ProcSet |-> << >>]
  /\ add_a = [p \in ProcSet |-> 0]
  /\ add_b = [p \in ProcSet |-> 0]
  /\ add_res = [p \in ProcSet |-> 0]
  /\ itos_i = [p \in ProcSet |-> 0]
  /\ itos_out = [p \in ProcSet |-> ""]
  /\ tmp = [p \in ProcSet |-> 0]
  /\ out = [p \in ProcSet |-> ""]
  /\ TypeOK

(*
  Control actions for the single fair process 0.
*)

A_Start ==
  /\ pc[0] = "start"
  /\ add_a' = [add_a EXCEPT ![0] = 7]
  /\ add_b' = [add_b EXCEPT ![0] = 3]
  /\ stack' =
      [stack EXCEPT
        ![0] = Append(@, [kind |-> "Add", retpc |-> "afterAdd",
                          a |-> add_a'[0], b |-> add_b'[0], res |-> 0])]
  /\ pc' = [pc EXCEPT ![0] = "add_0"]
  /\ UNCHANGED << add_res, itos_i, itos_out, tmp, out >>

A_Add0 ==
  /\ pc[0] = "add_0"
  /\ add_res' = [add_res EXCEPT ![0] = add_a[0] + add_b[0]]
  /\ pc' = [pc EXCEPT ![0] = "ret_add"]
  /\ UNCHANGED << stack, add_a, add_b, itos_i, itos_out, tmp, out >>

A_RetAdd ==
  /\ pc[0] = "ret_add"
  /\ Len(stack[0]) > 0
  /\ Top(stack[0]).kind = "Add"
  /\ LET fr == Top(stack[0])
         rest == Pop(stack[0])
     IN /\ tmp' = [tmp EXCEPT ![0] = add_res[0]]
        /\ stack' = [stack EXCEPT ![0] = rest]
        /\ pc' = [pc EXCEPT ![0] = fr.retpc]
        /\ UNCHANGED << add_a, add_b, add_res, itos_i, itos_out, out >>

A_AfterAdd ==
  /\ pc[0] = "afterAdd"
  /\ itos_i' = [itos_i EXCEPT ![0] = tmp[0]]
  /\ stack' =
      [stack EXCEPT
        ![0] = Append(@, [kind |-> "Str", retpc |-> "afterStr",
                          i |-> itos_i'[0], out |-> ""])]
  /\ pc' = [pc EXCEPT ![0] = "str_0"]
  /\ UNCHANGED << add_a, add_b, add_res, itos_out, tmp, out >>

A_Str0 ==
  /\ pc[0] = "str_0"
  /\ itos_i[0] = 10 \* assertion: the integer passed to string conversion is 10
  /\ itos_out' = [itos_out EXCEPT ![0] = IF itos_i[0] = 10 THEN "10" ELSE "not10"]
  /\ pc' = [pc EXCEPT ![0] = "ret_str"]
  /\ UNCHANGED << stack, add_a, add_b, add_res, itos_i, tmp, out >>

A_RetStr ==
  /\ pc[0] = "ret_str"
  /\ Len(stack[0]) > 0
  /\ Top(stack[0]).kind = "Str"
  /\ LET fr == Top(stack[0])
         rest == Pop(stack[0])
     IN /\ out' = [out EXCEPT ![0] = itos_out[0]]
        /\ stack' = [stack EXCEPT ![0] = rest]
        /\ pc' = [pc EXCEPT ![0] = fr.retpc]
        /\ UNCHANGED << add_a, add_b, add_res, itos_i, itos_out, tmp >>

A_AfterStr ==
  /\ pc[0] = "afterStr"
  /\ pc' = [pc EXCEPT ![0] = "Done"]
  /\ UNCHANGED << stack, add_a, add_b, add_res, itos_i, itos_out, tmp, out >>

ProcStep ==
  A_Start \/ A_Add0 \/ A_RetAdd \/ A_AfterAdd \/
  A_Str0  \/ A_RetStr \/ A_AfterStr

Next ==
  ProcStep \/ (/\ pc[0] = "Done" /\ UNCHANGED vars)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(ProcStep)

(*
  Safety invariants (assertions):
  - The integer passed to the string conversion is 10 when entering its body.
  - Upon termination, the final output string is "10".
*)
ArgIs10 ==
  (pc[0] = "str_0") => itos_i[0] = 10

FinalOutIs10 ==
  (pc[0] = "Done") => out[0] = "10"

(*
  Liveness properties:
  - Termination: eventually the process reaches Done.
  - Fairness-based progress: included via WF_vars(ProcStep) in Spec.
*)
Termination ==
  <> (pc[0] = "Done")
=============================================================================