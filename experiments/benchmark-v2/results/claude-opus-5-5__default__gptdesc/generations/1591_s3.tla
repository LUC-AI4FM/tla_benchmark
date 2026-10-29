------------------------------- MODULE EvenOdd -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

(* --algorithm EvenOdd
variable result = FALSE;

procedure Even(xEven = 0)
begin
  Even1: if xEven = 0 then
           result := TRUE;
           return;
         else
           call Odd(xEven - 1);
         end if;
  Even2: return;
end procedure

procedure Odd(xOdd = 0)
begin
  Odd1: if xOdd = 0 then
          result := FALSE;
          return;
        else
          call Even(xOdd - 1);
        end if;
  Odd2: return;
end procedure

begin
  EO1: call Even(N);
  EO2: print result;
end algorithm *)

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
        /\ pc = "EO1"

Even1 == /\ pc = "Even1"
         /\ IF xEven = 0
               THEN /\ result' = TRUE
                    /\ pc' = Head(stack).pc
                    /\ xEven' = Head(stack).xEven
                    /\ stack' = Tail(stack)
                    /\ xOdd' = xOdd
               ELSE /\ xOdd' = xEven - 1
                    /\ stack' = << [ procedure |-> "Odd",
                                     pc        |-> "Even2",
                                     xOdd      |-> xOdd ] >>
                                 \o stack
                    /\ pc' = "Odd1"
                    /\ UNCHANGED << result, xEven >>

Even2 == /\ pc = "Even2"
         /\ pc' = Head(stack).pc
         /\ xEven' = Head(stack).xEven
         /\ stack' = Tail(stack)
         /\ UNCHANGED << result, xOdd >>

Even == Even1 \/ Even2

Odd1 == /\ pc = "Odd1"
        /\ IF xOdd = 0
              THEN /\ result' = FALSE
                   /\ pc' = Head(stack).pc
                   /\ xOdd' = Head(stack).xOdd
                   /\ stack' = Tail(stack)
                   /\ xEven' = xEven
              ELSE /\ xEven' = xOdd - 1
                   /\ stack' = << [ procedure |-> "Even",
                                    pc        |-> "Odd2",
                                    xEven     |-> xEven ] >>
                                \o stack
                   /\ pc' = "Even1"
                   /\ UNCHANGED << result, xOdd >>

Odd2 == /\ pc = "Odd2"
        /\ pc' = Head(stack).pc
        /\ xOdd' = Head(stack).xOdd
        /\ stack' = Tail(stack)
        /\ UNCHANGED << result, xEven >>

Odd == Odd1 \/ Odd2

EO1 == /\ pc = "EO1"
       /\ xEven' = N
       /\ stack' = << [ procedure |-> "Even",
                        pc        |-> "EO2",
                        xEven     |-> xEven ] >>
                    \o stack
       /\ pc' = "Even1"
       /\ UNCHANGED << result, xOdd >>

EO2 == /\ pc = "EO2"
       /\ PrintT(result)
       /\ pc' = "Done"
       /\ UNCHANGED << result, stack, xEven, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ EO1 \/ EO2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

=============================================================================