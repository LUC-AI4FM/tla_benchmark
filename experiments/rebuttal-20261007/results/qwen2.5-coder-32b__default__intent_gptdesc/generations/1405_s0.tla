------------------------------- MODULE TwoComponentSystem -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    \* The specific nonzero value to set as result
    NEW_RESULT

VARIABLES 
    sequence, 
    result

Init == /\ sequence \in Seq(Nat)
        /\ Len(sequence) > 0
        /\ result = 0
        /\ \A x \in sequence: x > 0

InnerService ==
    /\ result = 0
    /\ result' = NEW_RESULT
    /\ sequence' = << s \in sequence : s # NEW_RESULT >>

Next == \/ InnerService
          \/ /\ result # 0
             /\ sequence' = sequence
             /\ result' = result

Spec == Init /\ [][Next]_<<sequence, result>>

\* Safety properties
Safety ==
    /\ \A s \in Seq(Nat) \X Nat: 
        /\ Len(s) > 0
        /\ \A x \in s: x > 0
        => \/ result = 0
           \/ /\ result = NEW_RESULT
              /\ sequence = << y \in s : y # NEW_RESULT >>

\* Liveness properties
Liveness ==
    <>[]<>(result = NEW_RESULT)

\* Progress/termination property
Progress ==
    <><>result # 0

Fairness == WF_<<sequence, result>>(InnerService)

=============================================================================