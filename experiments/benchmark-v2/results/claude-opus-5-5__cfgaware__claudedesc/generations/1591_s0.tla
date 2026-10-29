---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT N

(* --algorithm EvenOdd
variable result = FALSE;

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
  M1: call Even(N);
  M2: print result;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES pc, result, stack, xEven, xOdd

vars == << pc, result, stack, xEven, xOdd >>

Init == /\ result = FALSE
        /\ stack = << >>
        /\ xEven = 0
        /\ xOdd = 0
        /\ pc = "M1"

E1 == /\ pc = "E1"
      /\ IF xEven = 0
            THEN /\ result' = TRUE
                 /\ pc' = Head(stack).pc
                 /\ xEven' = Head(stack).xEven
                 /\ stack' = Tail(stack)
                 /\ xOdd' = xOdd
            ELSE /\ xOdd' = xEven - 1
                 /\ stack' = << [ procedure |-> "Odd",
                                  pc        |-> "E2",
                                  xOdd      |-> xOdd ] >>
                              \o stack
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
            ELSE /\ xEven' = xOdd - 1
                 /\ stack' = << [ procedure |-> "Even",
                                  pc        |-> "O2",
                                  xEven     |-> xEven ] >>
                              \o stack
                 /\ pc' = "E1"
                 /\ UNCHANGED << result, xOdd >>

O2 == /\ pc = "O2"
      /\ pc' = Head(stack).pc
      /\ xOdd' = Head(stack).xOdd
      /\ stack' = Tail(stack)
      /\ UNCHANGED << result, xEven >>

Odd == O1 \/ O2

M1 == /\ pc = "M1"
      /\ xEven' = N
      /\ stack' = << [ procedure |-> "Even",
                       pc        |-> "M2",
                       xEven     |-> xEven ] >>
                   \o stack
      /\ pc' = "E1"
      /\ UNCHANGED << result, xOdd >>

M2 == /\ pc = "M2"
      /\ PrintT(result)
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, xEven, xOdd >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ M1 \/ M2 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Auxiliary state predicates tracked as "possible" states. *)

\* The algorithm is currently executing the body of Odd.
InOdd == pc = "O1"

\* Even is about to (recursively) call Odd.
CallOdd == pc = "E1" /\ xEven # 0

\* Arguments with which Odd is invoked when computing Even(N):
\* N-1, N-3, ... down to 0 (only those that are >= 0).
OddArgs == { k \in 0..(N - 1) : (N - k) % 2 = 1 }

\* Arguments with which Even invokes Odd (Even(k) with k > 0):
\* N, N-2, ... down to 1.
EvenCallingArgs == { k \in 1..N : (N - k) % 2 = 0 }

\* Each predicate holds in exactly 3 distinct reachable states
\* (for N = 6: Odd(5), Odd(3), Odd(1); Even(6), Even(4), Even(2)).
PossibleCounts ==
    /\ Cardinality(OddArgs) = 3
    /\ Cardinality(EvenCallingArgs) = 3

=============================================================================