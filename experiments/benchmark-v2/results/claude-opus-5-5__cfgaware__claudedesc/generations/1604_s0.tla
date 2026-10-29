---------------------------- MODULE Playground ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES retval, output, pc, stack, a, b, n

vars == << retval, output, pc, stack, a, b, n >>

ProcSet == {1}

Init == (* Global variables *)
        /\ retval = defaultInitValue
        /\ output = defaultInitValue
        (* Procedure add *)
        /\ a = [ self \in ProcSet |-> defaultInitValue]
        /\ b = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure to_string *)
        /\ n = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Call1"]

AddLbl(self) == /\ pc[self] = "AddLbl"
                /\ retval' = a[self] + b[self]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << output, n >>

add(self) == AddLbl(self)

ToStr(self) == /\ pc[self] = "ToStr"
               /\ Assert(n[self] = 10,
                         "Failure of assertion in procedure to_string.")
               /\ retval' = "10"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << output, a, b >>

to_string(self) == ToStr(self)

Call1 == /\ pc[1] = "Call1"
         /\ /\ a' = [a EXCEPT ![1] = 3]
            /\ b' = [b EXCEPT ![1] = 7]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "add",
                                                  pc        |->  "Call2",
                                                  a         |->  a[1],
                                                  b         |->  b[1] ] >>
                                              \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "AddLbl"]
         /\ UNCHANGED << retval, output, n >>

Call2 == /\ pc[1] = "Call2"
         /\ /\ n' = [n EXCEPT ![1] = retval]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "to_string",
                                                  pc        |->  "Assign",
                                                  n         |->  n[1] ] >>
                                              \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "ToStr"]
         /\ UNCHANGED << retval, output, a, b >>

Assign == /\ pc[1] = "Assign"
          /\ output' = retval
          /\ pc' = [pc EXCEPT ![1] = "Check"]
          /\ UNCHANGED << retval, stack, a, b, n >>

Check == /\ pc[1] = "Check"
         /\ Assert(output = "10",
                   "Failure of assertion at label Check.")
         /\ pc' = [pc EXCEPT ![1] = "Done"]
         /\ UNCHANGED << retval, output, stack, a, b, n >>

main == Call1 \/ Call2 \/ Assign \/ Check

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: add(self) \/ to_string(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(main)
        /\ WF_vars(add(1))
        /\ WF_vars(to_string(1))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

Liveness == <>(\A self \in ProcSet: pc[self] = "Done")

=============================================================================