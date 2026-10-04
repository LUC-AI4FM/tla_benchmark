---------------------------- MODULE specification ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc, shared, local

vars == <<pc, shared, local>>

Procs == 0..(N-1)

LeftNeighbor(i) == (i - 1) % N

TypeOK ==
    /\ pc \in [Procs -> {"init", "writing", "written", "done"}]
    /\ shared \in [Procs -> [status : {"stable", "transitional"}, value : {0, 1}]]
    /\ local \in [Procs -> {0, 1}]

Init ==
    /\ pc = [i \in Procs |-> "init"]
    /\ shared = [i \in Procs |-> [status |-> "stable", value |-> 0]]
    /\ local = [i \in Procs |-> 0]

BeginWrite(i) ==
    /\ pc[i] = "init"
    /\ pc' = [pc EXCEPT ![i] = "writing"]
    /\ shared' = [shared EXCEPT ![i] = [status |-> "transitional", value |-> 1]]
    /\ local' = local

CompleteWrite(i) ==
    /\ pc[i] = "writing"
    /\ pc' = [pc EXCEPT ![i] = "written"]
    /\ shared' = [shared EXCEPT ![i] = [status |-> "stable", value |-> 1]]
    /\ local' = local

ReadNeighbor(i) ==
    /\ pc[i] = "written"
    /\ LET neighbor == LeftNeighbor(i)
           neighborShared == shared[neighbor]
       IN \/ /\ neighborShared.status = "stable"
             /\ local' = [local EXCEPT ![i] = neighborShared.value]
          \/ /\ neighborShared.status = "transitional"
             /\ \E v \in {0, 1} : local' = [local EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ shared' = shared

Next ==
    \E i \in Procs :
        \/ BeginWrite(i)
        \/ CompleteWrite(i)
        \/ ReadNeighbor(i)

Fairness == \A i \in Procs : WF_vars(BeginWrite(i)) /\ WF_vars(CompleteWrite(i)) /\ WF_vars(ReadNeighbor(i))

Spec == Init /\ [][Next]_vars /\ Fairness

AllDone == \A i \in Procs : pc[i] = "done"

AtLeastOneReadOne == \E i \in Procs : local[i] = 1

PCorrect == AllDone => AtLeastOneReadOne

SomeoneWritingOrWritten == \E i \in Procs : pc[i] \in {"writing", "written", "done"}

SomeoneWrittenOrDone == \E i \in Procs : pc[i] \in {"written", "done"}

WrittenImpliesStableOne(i) ==
    pc[i] \in {"written", "done"} => (shared[i].status = "stable" /\ shared[i].value = 1)

WritingImpliesTransitional(i) ==
    pc[i] = "writing" => (shared[i].status = "transitional" /\ shared[i].value = 1)

InitImpliesStableZero(i) ==
    pc[i] = "init" => (shared[i].status = "stable" /\ shared[i].value = 0)

SharedConsistency ==
    \A i \in Procs :
        /\ InitImpliesStableZero(i)
        /\ WritingImpliesTransitional(i)
        /\ WrittenImpliesStableOne(i)

FirstDoneProc ==
    IF \E i \in Procs : pc[i] = "done"
    THEN CHOOSE i \in Procs : pc[i] = "done" /\ \A j \in Procs : pc[j] = "done" => i <= j
    ELSE 0

ChainProperty ==
    \A i \in Procs :
        pc[i] = "done" =>
            LET neighbor == LeftNeighbor(i)
            IN pc[neighbor] \in {"writing", "written", "done"}

AllDoneImpliesSomeoneReadOne ==
    AllDone => AtLeastOneReadOne

ProgressInvariant ==
    (\E i \in Procs : pc[i] # "init") =>
    (\E i \in Procs : shared[i].value = 1)

Inv ==
    /\ TypeOK
    /\ SharedConsistency
    /\ ProgressInvariant
    /\ PCorrect

=============================================================================