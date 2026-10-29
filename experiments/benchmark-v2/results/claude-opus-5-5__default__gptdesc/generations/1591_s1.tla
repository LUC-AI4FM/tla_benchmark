------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME N \in Nat

(***************************************************************************
--algorithm EvenOdd
variable result = FALSE;

procedure Even (xEven = 0)
begin
  Even1: if xEven = 0 then
            result := TRUE;
            return;
         else
            call Odd(xEven - 1);
            return;
         end if;
end procedure

procedure Odd (xOdd = 0)
begin
  Odd1: if xOdd = 0 then
           result := FALSE;
        else
           call Even(xOdd - 1);
        end if;
  Odd2: return;
end procedure

begin
  EvenOdd1: call Even(N);
end algorithm
***************************************************************************)

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
        /\ pc = "EvenOdd1"

Even1 == /\ pc = "Even1"
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
                       /\ xEven' = Head(stack).xEven
                    /\ pc' = "Odd1"
                    /\ result' = result

Even == Even1

Odd1 == /\ pc = "Odd1"
        /\ IF xOdd = 0
              THEN /\ result' = FALSE
                   /\ pc' = "Odd2"
                   /\ UNCHANGED << stack, xEven >>
              ELSE /\ /\ stack' = << [ procedure |-> "Even",
                                       pc        |-> "Odd2",
                                       xEven     |-> xEven ] >>
                                   \o stack
                      /\ xEven' = xOdd - 1
                   /\ pc' = "Even1"
                   /\ result' = result
        /\ xOdd' = xOdd

Odd2 == /\ pc = "Odd2"
        /\ pc' = Head(stack).pc
        /\ xOdd' = Head(stack).xOdd
        /\ stack' = Tail(stack)
        /\ UNCHANGED << result, xEven >>

Odd == Odd1 \/ Odd2

EvenOdd1 == /\ pc = "EvenOdd1"
            /\ /\ stack' = << [ procedure |-> "Even",
                                pc        |-> "Done",
                                xEven     |-> xEven ] >>
                            \o stack
               /\ xEven' = N
            /\ pc' = "Even1"
            /\ UNCHANGED << result, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ EvenOdd1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================