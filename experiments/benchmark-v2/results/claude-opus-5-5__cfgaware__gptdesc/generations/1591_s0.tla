---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

PossibleCounts == 0..10

(***************************************************************************
--algorithm EvenOdd
variables result = FALSE;

procedure Even(xEven = 0)
begin
  E1: if xEven = 0 then
        result := TRUE;
        return;
      else
        call Odd(xEven - 1);
      end if;
  E2: return;
end procedure;

procedure Odd(xOdd = 0)
begin
  O1: if xOdd = 0 then
        result := FALSE;
        return;
      else
        call Even(xOdd - 1);
      end if;
  O2: return;
end procedure;

begin
  A1: call Even(N);
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES result, pc, stack, xEven, xOdd

vars == << result, pc, stack, xEven, xOdd >>

Init == /\ result = FALSE
        /\ xEven = 0
        /\ xOdd = 0
        /\ stack = << >>
        /\ pc = "A1"

E1 == /\ pc = "E1"
      /\ IF xEven = 0
            THEN /\ result' = TRUE
                 /\ pc' = Head(stack).pc
                 /\ xEven' = Head(stack).xEven
                 /\ stack' = Tail(stack)
                 /\ xOdd' = xOdd
            ELSE /\ /\ stack' = << [ procedure |-> "Odd",
                                     pc        |-> "E2",
                                     xOdd      |-> xOdd ] >>
                                 \o stack
                    /\ xOdd' = xEven - 1
                 /\ pc' = "O1"
                 /\ UNCHANGED << result, xEven >>

E2 == /\ pc = "E2"
      /\ pc' = Head(stack).pc
      /\ xEven' = Head(stack).xEven
      /\ stack' = Tail(stack)
      /\ UNCHANGED << result, xOdd >>

Even == E1 \/ E2

O1 == /\ pc = "O1"
      /\ IF xOdd = 0
            THEN /\ result' = FALSE
                 /\ pc' = Head(stack).pc
                 /\ xOdd' = Head(stack).xOdd
                 /\ stack' = Tail(stack)
                 /\ xEven' = xEven
            ELSE /\ /\ stack' = << [ procedure |-> "Even",
                                     pc        |-> "O2",
                                     xEven     |-> xEven ] >>
                                 \o stack
                    /\ xEven' = xOdd - 1
                 /\ pc' = "E1"
                 /\ UNCHANGED << result, xOdd >>

O2 == /\ pc = "O2"
      /\ pc' = Head(stack).pc
      /\ xOdd' = Head(stack).xOdd
      /\ stack' = Tail(stack)
      /\ UNCHANGED << result, xEven >>

Odd == O1 \/ O2

A1 == /\ pc = "A1"
      /\ /\ stack' = << [ procedure |-> "Even",
                          pc        |-> "Done",
                          xEven     |-> xEven ] >>
                      \o stack
         /\ xEven' = N
      /\ pc' = "E1"
      /\ UNCHANGED << result, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ A1 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================