---------------------------- MODULE Playground ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

(* --algorithm Playground
variables retval = 0, output = "";

procedure add(a, b)
begin
  Add1:
    retval := a + b;
    return;
end procedure;

procedure to_string(n)
begin
  ToString1:
    assert n = 10;
    retval := "10";
    return;
end procedure;

fair process main = 1
begin
  Lbl_1:
    call add(3, 7);
  Lbl_2:
    call to_string(retval);
  Lbl_3:
    output := retval;
  Lbl_4:
    assert output = "10";
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES retval, output, pc, stack, a, b, n

vars == << retval, output, pc, stack, a, b, n >>

ProcSet == {1}

Init == (* Global variables *)
        /\ retval = 0
        /\ output = ""
        (* Procedure add *)
        /\ a = [ self \in ProcSet |-> defaultInitValue]
        /\ b = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure to_string *)
        /\ n = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Lbl_1"]

Add1(self) == /\ pc[self] = "Add1"
              /\ retval' = a[self] + b[self]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
              /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << output, n >>

add(self) == Add1(self)

ToString1(self) == /\ pc[self] = "ToString1"
                   /\ Assert(n[self] = 10,
                             "Failure of assertion at line 17, column 5.")
                   /\ retval' = "10"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << output, a, b >>

to_string(self) == ToString1(self)

Lbl_1 == /\ pc[1] = "Lbl_1"
         /\ /\ a' = [a EXCEPT ![1] = 3]
            /\ b' = [b EXCEPT ![1] = 7]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "add",
                                                   pc        |-> "Lbl_2",
                                                   a         |-> a[1],
                                                   b         |-> b[1] ] >>
                                               \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "Add1"]
         /\ UNCHANGED << retval, output, n >>

Lbl_2 == /\ pc[1] = "Lbl_2"
         /\ /\ n' = [n EXCEPT ![1] = retval]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "to_string",
                                                   pc        |-> "Lbl_3",
                                                   n         |-> n[1] ] >>
                                               \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "ToString1"]
         /\ UNCHANGED << retval, output, a, b >>

Lbl_3 == /\ pc[1] = "Lbl_3"
         /\ output' = retval
         /\ pc' = [pc EXCEPT ![1] = "Lbl_4"]
         /\ UNCHANGED << retval, stack, a, b, n >>

Lbl_4 == /\ pc[1] = "Lbl_4"
         /\ Assert(output = "10",
                   "Failure of assertion at line 34, column 5.")
         /\ pc' = [pc EXCEPT ![1] = "Done"]
         /\ UNCHANGED << retval, output, stack, a, b, n >>

main == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: add(self) \/ to_string(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(main) /\ WF_vars(add(1)) /\ WF_vars(to_string(1))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* Liveness property checked by the model: the process eventually finishes *)
Liveness == <>(pc[1] = "Done")

=============================================================================