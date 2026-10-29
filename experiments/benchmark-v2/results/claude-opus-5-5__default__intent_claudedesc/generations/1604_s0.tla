------------------------------ MODULE ProcedureReturnValues ------------------------------
(***************************************************************************)
(* A demonstration of procedural composition in PlusCal, where procedures  *)
(* "return" values by writing to a shared variable `ret`.                  *)
(*                                                                         *)
(* --algorithm ProcedureReturnValues                                       *)
(* variables ret = defaultInitValue, output = defaultInitValue;            *)
(*                                                                         *)
(* procedure Add(a, b)                                                     *)
(* begin                                                                   *)
(*   Add1: ret := a + b;                                                   *)
(*         return;                                                         *)
(* end procedure;                                                          *)
(*                                                                         *)
(* procedure ToString(n)                                                   *)
(* begin                                                                   *)
(*   TS1: if n = 10 then ret := "10" else ret := "unknown" end if;         *)
(*        return;                                                          *)
(* end procedure;                                                          *)
(*                                                                         *)
(* begin                                                                   *)
(*   Lbl_1: call Add(3, 7);                                                *)
(*   Lbl_2: assert ret = 10;                                               *)
(*          call ToString(ret);                                            *)
(*   Lbl_3: output := ret;                                                 *)
(*          assert output = "10";                                          *)
(* end algorithm;                                                          *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES ret, output, pc, stack, a, b, n

vars == << ret, output, pc, stack, a, b, n >>

Init ==
    /\ ret = defaultInitValue
    /\ output = defaultInitValue
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ n = defaultInitValue
    /\ stack = << >>
    /\ pc = "Lbl_1"

(* Procedure Add: stores a + b into ret, then returns *)
Add1 ==
    /\ pc = "Add1"
    /\ ret' = a + b
    /\ pc' = Head(stack).pc
    /\ a' = Head(stack).a
    /\ b' = Head(stack).b
    /\ stack' = Tail(stack)
    /\ UNCHANGED << output, n >>

Add == Add1

(* Procedure ToString: stores string form of n into ret, then returns *)
TS1 ==
    /\ pc = "TS1"
    /\ IF n = 10
          THEN ret' = "10"
          ELSE ret' = "unknown"
    /\ pc' = Head(stack).pc
    /\ n' = Head(stack).n
    /\ stack' = Tail(stack)
    /\ UNCHANGED << output, a, b >>

ToString == TS1

(* Main body *)
Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ a' = 3
    /\ b' = 7
    /\ stack' = << [ procedure |-> "Add",
                     pc        |-> "Lbl_2",
                     a         |-> a,
                     b         |-> b ] >> \o stack
    /\ pc' = "Add1"
    /\ UNCHANGED << ret, output, n >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ Assert(ret = 10, "Failure of assertion: Add(3, 7) did not return 10")
    /\ n' = ret
    /\ stack' = << [ procedure |-> "ToString",
                     pc        |-> "Lbl_3",
                     n         |-> n ] >> \o stack
    /\ pc' = "TS1"
    /\ UNCHANGED << ret, output, a, b >>

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ output' = ret
    /\ Assert(output' = "10", "Failure of assertion: output is not \"10\"")
    /\ pc' = "Done"
    /\ UNCHANGED << ret, stack, a, b, n >>

(* Allow infinite stuttering to prevent deadlock on termination *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Add \/ ToString \/ Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

PCOK ==
    pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Add1", "TS1", "Done"}

(* Intermediate value: after Add returns, ret holds 10 *)
AddResultCorrect ==
    pc = "Lbl_2" => ret = 10

(* Intermediate value: ToString is invoked with argument 10 *)
ToStringArgCorrect ==
    pc = "TS1" => n = 10

(* Final value: on completion, output equals "10" *)
OutputCorrect ==
    pc = "Done" => output = "10"

(* Call stack depth never exceeds one in this program *)
StackBounded ==
    Len(stack) <= 1

Invariants ==
    /\ PCOK
    /\ AddResultCorrect
    /\ ToStringArgCorrect
    /\ OutputCorrect
    /\ StackBounded

-----------------------------------------------------------------------------
(* Liveness: the process eventually completes *)

Termination == <>(pc = "Done")

=============================================================================