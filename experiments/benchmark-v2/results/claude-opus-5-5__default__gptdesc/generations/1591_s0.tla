------------------------------- MODULE EvenOdd -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat

(* --algorithm EvenOdd {
    variable result = FALSE;

    procedure Even (xEven = 0) {
      e1: if (xEven = 0) {
            result := TRUE;
            return;
          } else {
            call Odd(xEven - 1);
            return;
          }
    }

    procedure Odd (xOdd = 0) {
      o1: if (xOdd = 0) {
            result := FALSE;
            return;
          } else {
            call Even(xOdd - 1);
            return;
          }
    }

    {
      a1: call Even(N);
    }
} *)

\* BEGIN TRANSLATION
VARIABLES result, pc, stack, xEven, xOdd

vars == << result, pc, stack, xEven, xOdd >>

Init == (* Global variables *)
        /\ result = FALSE
        (* Procedure Even *)
        /\ xEven = 0
        (* Procedure Odd *)
        /\ xOdd = 0
        /\ stack = << >>
        /\ pc = "a1"

e1 == /\ pc = "e1"
      /\ IF xEven = 0
            THEN /\ result' = TRUE
                 /\ pc' = Head(stack).pc
                 /\ xEven' = Head(stack).xEven
                 /\ stack' = Tail(stack)
                 /\ xOdd' = xOdd
            ELSE /\ /\ stack' = << [ procedure |-> "Odd",
                                     pc        |-> Head(stack).pc,
                                     xOdd      |-> xOdd ] >>
                                 \o Tail(stack)
                    /\ xOdd' = xEven - 1
                 /\ pc' = "o1"
                 /\ xEven' = Head(stack).xEven
                 /\ result' = result

Even == e1

o1 == /\ pc = "o1"
      /\ IF xOdd = 0
            THEN /\ result' = FALSE
                 /\ pc' = Head(stack).pc
                 /\ xOdd' = Head(stack).xOdd
                 /\ stack' = Tail(stack)
                 /\ xEven' = xEven
            ELSE /\ /\ stack' = << [ procedure |-> "Even",
                                     pc        |-> Head(stack).pc,
                                     xEven     |-> xEven ] >>
                                 \o Tail(stack)
                    /\ xEven' = xOdd - 1
                 /\ pc' = "e1"
                 /\ xOdd' = Head(stack).xOdd
                 /\ result' = result

Odd == o1

a1 == /\ pc = "a1"
      /\ /\ stack' = << [ procedure |-> "Even",
                          pc        |-> "Done",
                          xEven     |-> xEven ] >>
                      \o stack
         /\ xEven' = N
      /\ pc' = "e1"
      /\ UNCHANGED << result, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ a1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================