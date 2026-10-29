------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME NInNat == N \in Nat

(* Initialise TLC registers used to count the distinct states in which
   the auxiliary predicates InOdd and CallOdd hold. *)
ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, 0)

(***************************************************************************
--algorithm EvenOdd {
    variable result = FALSE;

    procedure Even(xEven = 0) {
        Even1: if (xEven = 0) {
                    result := TRUE;
                    return;
               } else {
                    call Odd(xEven - 1);
                    return;
               }
    }

    procedure Odd(xOdd = 0) {
        Odd1: if (xOdd = 0) {
                    result := FALSE;
                    return;
              } else {
                    call Even(xOdd - 1);
                    return;
              }
    }

    {
        a1: call Even(N);
        a2: print result;
    }
}
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
        /\ pc = "a1"

Even1 == /\ pc = "Even1"
         /\ IF xEven = 0
               THEN /\ result' = TRUE
                    /\ pc' = Head(stack).pc
                    /\ xEven' = Head(stack).xEven
                    /\ stack' = Tail(stack)
                    /\ xOdd' = xOdd
               ELSE /\ xOdd' = xEven - 1
                    /\ stack' = << [ procedure |-> "Odd",
                                     pc        |-> Head(stack).pc,
                                     xOdd      |-> xOdd ] >>
                                 \o Tail(stack)
                    /\ xEven' = Head(stack).xEven
                    /\ pc' = "Odd1"
                    /\ UNCHANGED result

Even == Even1

Odd1 == /\ pc = "Odd1"
        /\ IF xOdd = 0
              THEN /\ result' = FALSE
                   /\ pc' = Head(stack).pc
                   /\ xOdd' = Head(stack).xOdd
                   /\ stack' = Tail(stack)
                   /\ xEven' = xEven
              ELSE /\ xEven' = xOdd - 1
                   /\ stack' = << [ procedure |-> "Even",
                                    pc        |-> Head(stack).pc,
                                    xEven     |-> xEven ] >>
                                \o Tail(stack)
                   /\ xOdd' = Head(stack).xOdd
                   /\ pc' = "Even1"
                   /\ UNCHANGED result

Odd == Odd1

a1 == /\ pc = "a1"
      /\ xEven' = N
      /\ stack' = << [ procedure |-> "Even",
                       pc        |-> "a2",
                       xEven     |-> xEven ] >>
                   \o stack
      /\ pc' = "Even1"
      /\ UNCHANGED << result, xOdd >>

a2 == /\ pc = "a2"
      /\ PrintT(result)
      /\ pc' = "Done"
      /\ UNCHANGED << result, stack, xEven, xOdd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Even \/ Odd \/ a1 \/ a2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK == /\ result \in BOOLEAN
          /\ pc \in {"a1", "a2", "Even1", "Odd1", "Done"}
          /\ xEven \in Nat
          /\ xOdd \in Nat
          /\ stack \in Seq([procedure : {"Even", "Odd"},
                            pc        : {"a2"},
                            xEven     : Nat] \cup
                           [procedure : {"Even", "Odd"},
                            pc        : {"a2"},
                            xOdd      : Nat])

(* Upon termination the result reflects the parity of N. *)
Correctness == (pc = "Done") => (result = (N % 2 = 0))

-----------------------------------------------------------------------------
(* Auxiliary predicates tracked via TLC's _POSSIBLE directive.            *)

\* _POSSIBLE InOdd
InOdd == pc = "Odd1"

\* _POSSIBLE CallOdd
CallOdd == pc = "Even1" /\ xEven # 0

(* State constraint used to count the distinct states satisfying each of
   the _POSSIBLE predicates (TLC evaluates the constraint once per newly
   generated distinct state). *)
PossibleConstraint ==
    /\ IF InOdd   THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF CallOdd THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

(* Postcondition: computing Even(6) involves exactly 3 calls to Odd, so
   each predicate is observed in exactly 3 distinct states. *)
PossibleCounts ==
    /\ TLCGet(1) = 3
    /\ TLCGet(2) = 3

=============================================================================