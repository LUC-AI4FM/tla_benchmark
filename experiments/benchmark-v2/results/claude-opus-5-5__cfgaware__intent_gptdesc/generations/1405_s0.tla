---------------------------- MODULE InnerOuterService ----------------------------
EXTENDS Integers, Sequences

VARIABLES result, seq

vars == <<result, seq>>

\* The fixed nonzero value the inner service writes into the result.
NewVal == 1

\* The initial finite nonempty sequence of positive integers.
InitSeq == <<1, 2, 3>>

NotNewVal(x) == x # NewVal

\* The sequence with all occurrences of NewVal removed.
Remove(s) == SelectSeq(s, NotNewVal)

-----------------------------------------------------------------------------
\* Inner service component, operating on the shared result and sequence.

InnerInit == /\ result = 0
             /\ seq = InitSeq

InnerNext == /\ result = 0
             /\ result' = NewVal
             /\ seq' = Remove(seq)

-----------------------------------------------------------------------------
\* Outer controller: it stutters whenever the inner service is disabled.

Init == InnerInit

OuterStutter == /\ ~ENABLED InnerNext
                /\ UNCHANGED vars

Next == InnerNext \/ OuterStutter

\* The inner service is fair: weak fairness on its atomic action.
Spec == Init /\ [][Next]_vars /\ WF_vars(InnerNext)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK == /\ result \in Int
          /\ seq \in Seq(Int)

\* The result is either the initial zero or the specified nonzero value.
ResultOK == result \in {0, NewVal}

\* The sequence is the original sequence, or that sequence with every
\* occurrence of NewVal removed.
SeqOK == seq \in {InitSeq, Remove(InitSeq)}

\* The result and the sequence change together, as one atomic update.
Consistent == /\ (result = 0) => (seq = InitSeq)
              /\ (result = NewVal) => (seq = Remove(InitSeq))

Safety == TypeOK /\ ResultOK /\ SeqOK /\ Consistent

\* The result only changes from 0 to NewVal, never to any other value.
ResultTransition == [][result # result' => (result = 0 /\ result' = NewVal)]_vars

\* Once the result has been updated, it stays updated.
ResultStable == [][result = NewVal => result' = NewVal]_vars

-----------------------------------------------------------------------------
\* Liveness and termination properties

\* The inner service eventually executes.
EventuallyDone == <>(result = NewVal /\ seq = Remove(InitSeq))

\* The system reaches a stable state where no inner action is enabled.
\* From then on, every step is a stutter.
SpecRunsToEnd == <>[](~ENABLED InnerNext)

Termination == <>[](result = NewVal /\ seq = Remove(InitSeq)
                     /\ ~ENABLED InnerNext)

THEOREM Spec => []Safety
THEOREM Spec => ResultTransition /\ ResultStable
THEOREM Spec => EventuallyDone
THEOREM Spec => SpecRunsToEnd
THEOREM Spec => Termination
=============================================================================